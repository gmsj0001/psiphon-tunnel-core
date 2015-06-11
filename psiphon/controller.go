/*
 * Copyright (c) 2015, Psiphon Inc.
 * All rights reserved.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

// Package psiphon implements the core tunnel functionality of a Psiphon client.
// The main function is RunForever, which runs a Controller that obtains lists of
// servers, establishes tunnel connections, and runs local proxies through which
// tunneled traffic may be sent.
package psiphon

import (
	"errors"
	"net"
	"sync"
	"time"
)

// Controller is a tunnel lifecycle coordinator. It manages lists of servers to
// connect to; establishes and monitors tunnels; and runs local proxies which
// route traffic through the tunnels.
type Controller struct {
	config                      *Config
	sessionId                   string
	componentFailureSignal      chan struct{}
	shutdownBroadcast           chan struct{}
	runWaitGroup                *sync.WaitGroup
	establishedTunnels          chan *Tunnel
	failedTunnels               chan *Tunnel
	tunnelMutex                 sync.Mutex
	establishedOnce             bool
	tunnels                     []*Tunnel
	nextTunnel                  int
	startedConnectedReporter    bool
	isEstablishing              bool
	establishWaitGroup          *sync.WaitGroup
	stopEstablishingBroadcast   chan struct{}
	candidateServerEntries      chan *ServerEntry
	establishPendingConns       *Conns
	untunneledPendingConns      *Conns
	untunneledDialConfig        *DialConfig
	signalFetchRemoteServerList chan struct{}
}

// NewController initializes a new controller.
func NewController(config *Config) (controller *Controller, err error) {

	// Generate a session ID for the Psiphon server API. This session ID is
	// used across all tunnels established by the controller.
	sessionId, err := MakeSessionId()
	if err != nil {
		return nil, ContextError(err)
	}

	// untunneledPendingConns may be used to interrupt the fetch remote server list
	// request and other untunneled connection establishments. BindToDevice may be
	// used to exclude these requests and connection from VPN routing.
	untunneledPendingConns := new(Conns)
	untunneledDialConfig := &DialConfig{
		UpstreamHttpProxyAddress: config.UpstreamHttpProxyAddress,
		PendingConns:             untunneledPendingConns,
		DeviceBinder:             config.DeviceBinder,
		DnsServerGetter:          config.DnsServerGetter,
		ConnectTimeout:			time.Second * 1,
	}

	controller = &Controller{
		config:    config,
		sessionId: sessionId,
		// componentFailureSignal receives a signal from a component (including socks and
		// http local proxies) if they unexpectedly fail. Senders should not block.
		// A buffer allows at least one stop signal to be sent before there is a receiver.
		componentFailureSignal: make(chan struct{}, 1),
		shutdownBroadcast:      make(chan struct{}),
		runWaitGroup:           new(sync.WaitGroup),
		// establishedTunnels and failedTunnels buffer sizes are large enough to
		// receive full pools of tunnels without blocking. Senders should not block.
		establishedTunnels:       make(chan *Tunnel, config.TunnelPoolSize),
		failedTunnels:            make(chan *Tunnel, config.TunnelPoolSize),
		tunnels:                  make([]*Tunnel, 0),
		establishedOnce:          false,
		startedConnectedReporter: false,
		isEstablishing:           false,
		establishPendingConns:    new(Conns),
		untunneledPendingConns:   untunneledPendingConns,
		untunneledDialConfig:     untunneledDialConfig,
		// A buffer allows at least one signal to be sent even when the receiver is
		// not listening. Senders should not block.
		signalFetchRemoteServerList: make(chan struct{}, 1),
	}

	NewSplitTunnelClassifier(config, controller)

	return controller, nil
}

// Run executes the controller. It launches components and then monitors
// for a shutdown signal; after receiving the signal it shuts down the
// controller.
// The components include:
// - the periodic remote server list fetcher
// - the connected reporter
// - the tunnel manager
// - a local SOCKS proxy that port forwards through the pool of tunnels
// - a local HTTP proxy that port forwards through the pool of tunnels
func (controller *Controller) Run(shutdownBroadcast <-chan struct{}) {
	NoticeBuildInfo()
	NoticeCoreVersion(VERSION)
	ReportAvailableRegions()

	// Start components

	socksProxy, err := NewSocksProxy(controller.config, controller)
	if err != nil {
		NoticeAlert("error initializing local SOCKS proxy: %s", err)
		return
	}
	defer socksProxy.Close()

	httpProxy, err := NewHttpProxy(
		controller.config, controller.untunneledDialConfig, controller)
	if err != nil {
		NoticeAlert("error initializing local HTTP proxy: %s", err)
		return
	}
	defer httpProxy.Close()

	if !controller.config.DisableRemoteServerListFetcher {
		controller.runWaitGroup.Add(1)
		go controller.remoteServerListFetcher()
	}

	/// Note: the connected reporter isn't started until a tunnel is
	// established

	controller.runWaitGroup.Add(1)
	go controller.runTunnels()

	if *controller.config.EstablishTunnelTimeoutSeconds != 0 {
		controller.runWaitGroup.Add(1)
		go controller.establishTunnelWatcher()
	}

	// Wait while running

	select {
	case <-shutdownBroadcast:
		NoticeInfo("controller shutdown by request")
	case <-controller.componentFailureSignal:
		NoticeAlert("controller shutdown due to component failure")
	}

	close(controller.shutdownBroadcast)
	controller.establishPendingConns.CloseAll()
	controller.untunneledPendingConns.CloseAll()
	controller.runWaitGroup.Wait()

	splitTunnelClassifier.Shutdown()

	NoticeInfo("exiting controller")
}

// SignalComponentFailure notifies the controller that an associated component has failed.
// This will terminate the controller.
func (controller *Controller) SignalComponentFailure() {
	select {
	case controller.componentFailureSignal <- *new(struct{}):
	default:
	}
}

// remoteServerListFetcher fetches an out-of-band list of server entries
// for more tunnel candidates. It fetches when signalled, with retries
// on failure.
func (controller *Controller) remoteServerListFetcher() {
	defer controller.runWaitGroup.Done()

	var lastFetchTime time.Time

fetcherLoop:
	for {
		// Wait for a signal before fetching
		select {
		case <-controller.signalFetchRemoteServerList:
		case <-controller.shutdownBroadcast:
			break fetcherLoop
		}

		// Skip fetch entirely (i.e., send no request at all, even when ETag would save
		// on response size) when a recent fetch was successful
		if time.Now().Before(lastFetchTime.Add(FETCH_REMOTE_SERVER_LIST_STALE_PERIOD)) {
			continue
		}

	retryLoop:
		for {
			// Don't attempt to fetch while there is no network connectivity,
			// to avoid alert notice noise.
			if !WaitForNetworkConnectivity(
				controller.config.NetworkConnectivityChecker,
				controller.shutdownBroadcast) {
				break fetcherLoop
			}

			err := FetchRemoteServerList(
				controller.config, controller.untunneledDialConfig)

			if err == nil {
				lastFetchTime = time.Now()
				break retryLoop
			}

			NoticeAlert("failed to fetch remote server list: %s", err)

			timeout := time.After(FETCH_REMOTE_SERVER_LIST_RETRY_PERIOD)
			select {
			case <-timeout:
			case <-controller.shutdownBroadcast:
				break fetcherLoop
			}
		}
	}

	NoticeInfo("exiting remote server list fetcher")
}

// establishTunnelWatcher terminates the controller if a tunnel
// has not been established in the configured time period. This
// is regardless of how many tunnels are presently active -- meaning
// that if an active tunnel was established and lost the controller
// is left running (to re-establish).
func (controller *Controller) establishTunnelWatcher() {
	defer controller.runWaitGroup.Done()

	timeout := time.After(
		time.Duration(*controller.config.EstablishTunnelTimeoutSeconds) * time.Second)
	select {
	case <-timeout:
		if !controller.hasEstablishedOnce() {
			NoticeAlert("failed to establish tunnel before timeout")
			controller.SignalComponentFailure()
		}
	case <-controller.shutdownBroadcast:
	}

	NoticeInfo("exiting establish tunnel watcher")
}

// connectedReporter sends periodic "connected" requests to the Psiphon API.
// These requests are for server-side unique user stats calculation. See the
// comment in DoConnectedRequest for a description of the request mechanism.
// To ensure we don't over- or under-count unique users, only one connected
// request is made across all simultaneous multi-tunnels; and the connected
// request is repeated periodically.
func (controller *Controller) connectedReporter() {
	defer controller.runWaitGroup.Done()
loop:
	for {

		// Pick any active tunnel and make the next connected request. No error
		// is logged if there's no active tunnel, as that's not an unexpected condition.
		reported := false
		tunnel := controller.getNextActiveTunnel()
		if tunnel != nil {
			err := tunnel.session.DoConnectedRequest()
			if err == nil {
				reported = true
			} else {
				NoticeAlert("failed to make connected request: %s", err)
			}
		}

		// Schedule the next connected request and wait.
		var duration time.Duration
		if reported {
			duration = PSIPHON_API_CONNECTED_REQUEST_PERIOD
		} else {
			duration = PSIPHON_API_CONNECTED_REQUEST_RETRY_PERIOD
		}
		timeout := time.After(duration)
		select {
		case <-timeout:
			// Make another connected request
		case <-controller.shutdownBroadcast:
			break loop
		}
	}

	NoticeInfo("exiting connected reporter")
}

func (controller *Controller) startConnectedReporter() {
	if controller.config.DisableApi {
		return
	}

	// Start the connected reporter after the first tunnel is established.
	// Concurrency note: only the runTunnels goroutine may access startedConnectedReporter.
	if !controller.startedConnectedReporter {
		controller.startedConnectedReporter = true
		controller.runWaitGroup.Add(1)
		go controller.connectedReporter()
	}
}

// runTunnels is the controller tunnel management main loop. It starts and stops
// establishing tunnels based on the target tunnel pool size and the current size
// of the pool. Tunnels are established asynchronously using worker goroutines.
//
// When there are no server entries for the target region/protocol, the
// establishCandidateGenerator will yield no candidates and wait before
// trying again. In the meantime, a remote server entry fetch may supply
// valid candidates.
//
// When a tunnel is established, it's added to the active pool. The tunnel's
// operateTunnel goroutine monitors the tunnel.
//
// When a tunnel fails, it's removed from the pool and the establish process is
// restarted to fill the pool.
func (controller *Controller) runTunnels() {
	defer controller.runWaitGroup.Done()

	// Start running

	controller.startEstablishing()
loop:
	for {
		select {
		case failedTunnel := <-controller.failedTunnels:
			NoticeAlert("tunnel failed: %s", failedTunnel.serverEntry.IpAddress)
			controller.terminateTunnel(failedTunnel)
			// Concurrency note: only this goroutine may call startEstablishing/stopEstablishing
			// and access isEstablishing.
			if !controller.isEstablishing {
				controller.startEstablishing()
			}

		// !TODO! design issue: might not be enough server entries with region/caps to ever fill tunnel slots
		// solution(?) target MIN(CountServerEntries(region, protocol), TunnelPoolSize)
		case establishedTunnel := <-controller.establishedTunnels:
			if controller.registerTunnel(establishedTunnel) {
				NoticeActiveTunnel(establishedTunnel.serverEntry.IpAddress)
			} else {
				controller.discardTunnel(establishedTunnel)
			}
			if controller.isFullyEstablished() {
				controller.stopEstablishing()
			}
			controller.startConnectedReporter()

		case <-controller.shutdownBroadcast:
			break loop
		}
	}

	// Stop running

	controller.stopEstablishing()
	controller.terminateAllTunnels()

	// Drain tunnel channels
	close(controller.establishedTunnels)
	for tunnel := range controller.establishedTunnels {
		controller.discardTunnel(tunnel)
	}
	close(controller.failedTunnels)
	for tunnel := range controller.failedTunnels {
		controller.discardTunnel(tunnel)
	}

	NoticeInfo("exiting run tunnels")
}

// SignalTunnelFailure implements the TunnelOwner interface. This function
// is called by Tunnel.operateTunnel when the tunnel has detected that it
// has failed. The Controller will signal runTunnels to create a new
// tunnel and/or remove the tunnel from the list of active tunnels.
func (controller *Controller) SignalTunnelFailure(tunnel *Tunnel) {
	// Don't block. Assumes the receiver has a buffer large enough for
	// the typical number of operated tunnels. In case there's no room,
	// terminate the tunnel (runTunnels won't get a signal in this case,
	// but the tunnel will be removed from the list of active tunnels).
	select {
	case controller.failedTunnels <- tunnel:
	default:
		controller.terminateTunnel(tunnel)
	}
}

// discardTunnel disposes of a successful connection that is no longer required.
func (controller *Controller) discardTunnel(tunnel *Tunnel) {
	NoticeInfo("discard tunnel: %s", tunnel.serverEntry.IpAddress)
	// TODO: not calling PromoteServerEntry, since that would rank the
	// discarded tunnel before fully active tunnels. Can a discarded tunnel
	// be promoted (since it connects), but with lower rank than all active
	// tunnels?
	tunnel.Close()
}

// registerTunnel adds the connected tunnel to the pool of active tunnels
// which are candidates for port forwarding. Returns true if the pool has an
// empty slot and false if the pool is full (caller should discard the tunnel).
func (controller *Controller) registerTunnel(tunnel *Tunnel) bool {
	controller.tunnelMutex.Lock()
	defer controller.tunnelMutex.Unlock()
	if len(controller.tunnels) >= controller.config.TunnelPoolSize {
		return false
	}
	// Perform a final check just in case we've established
	// a duplicate connection.
	for _, activeTunnel := range controller.tunnels {
		if activeTunnel.serverEntry.IpAddress == tunnel.serverEntry.IpAddress {
			NoticeAlert("duplicate tunnel: %s", tunnel.serverEntry.IpAddress)
			return false
		}
	}
	controller.establishedOnce = true
	controller.tunnels = append(controller.tunnels, tunnel)
	NoticeTunnels(len(controller.tunnels))

	// The split tunnel classifier is started once the first tunnel is
	// established. This first tunnel is passed in to be used to make
	// the routes data request.
	// A long-running controller may run while the host device is present
	// in different regions. In this case, we want the split tunnel logic
	// to switch to routes for new regions and not classify traffic based
	// on routes installed for older regions.
	// We assume that when regions change, the host network will also
	// change, and so all tunnels will fail and be re-established. Under
	// that assumption, the classifier will be re-Start()-ed here when
	// the region has changed.
	if len(controller.tunnels) == 1 {
		splitTunnelClassifier.Start(tunnel)
	}

	return true
}

// hasEstablishedOnce indicates if at least one active tunnel has
// been established up to this point. This is regardeless of how many
// tunnels are presently active.
func (controller *Controller) hasEstablishedOnce() bool {
	controller.tunnelMutex.Lock()
	defer controller.tunnelMutex.Unlock()
	return controller.establishedOnce
}

// isFullyEstablished indicates if the pool of active tunnels is full.
func (controller *Controller) isFullyEstablished() bool {
	controller.tunnelMutex.Lock()
	defer controller.tunnelMutex.Unlock()
	return len(controller.tunnels) >= controller.config.TunnelPoolSize
}

// terminateTunnel removes a tunnel from the pool of active tunnels
// and closes the tunnel. The next-tunnel state used by getNextActiveTunnel
// is adjusted as required.
func (controller *Controller) terminateTunnel(tunnel *Tunnel) {
	controller.tunnelMutex.Lock()
	defer controller.tunnelMutex.Unlock()
	for index, activeTunnel := range controller.tunnels {
		if tunnel == activeTunnel {
			controller.tunnels = append(
				controller.tunnels[:index], controller.tunnels[index+1:]...)
			if controller.nextTunnel > index {
				controller.nextTunnel--
			}
			if controller.nextTunnel >= len(controller.tunnels) {
				controller.nextTunnel = 0
			}
			activeTunnel.Close()
			NoticeTunnels(len(controller.tunnels))
			break
		}
	}
}

// terminateAllTunnels empties the tunnel pool, closing all active tunnels.
// This is used when shutting down the controller.
func (controller *Controller) terminateAllTunnels() {
	controller.tunnelMutex.Lock()
	defer controller.tunnelMutex.Unlock()
	// Closing all tunnels in parallel. In an orderly shutdown, each tunnel
	// may take a few seconds to send a final status request. We only want
	// to wait as long as the single slowest tunnel.
	closeWaitGroup := new(sync.WaitGroup)
	closeWaitGroup.Add(len(controller.tunnels))
	for _, activeTunnel := range controller.tunnels {
		tunnel := activeTunnel
		go func() {
			defer closeWaitGroup.Done()
			tunnel.Close()
		}()
	}
	closeWaitGroup.Wait()
	controller.tunnels = make([]*Tunnel, 0)
	controller.nextTunnel = 0
	NoticeTunnels(len(controller.tunnels))
}

// getNextActiveTunnel returns the next tunnel from the pool of active
// tunnels. Currently, tunnel selection order is simple round-robin.
func (controller *Controller) getNextActiveTunnel() (tunnel *Tunnel) {
	controller.tunnelMutex.Lock()
	defer controller.tunnelMutex.Unlock()
	for i := len(controller.tunnels); i > 0; i-- {
		tunnel = controller.tunnels[controller.nextTunnel]
		controller.nextTunnel =
			(controller.nextTunnel + 1) % len(controller.tunnels)
		return tunnel
	}
	return nil
}

// isActiveTunnelServerEntry is used to check if there's already
// an existing tunnel to a candidate server.
func (controller *Controller) isActiveTunnelServerEntry(serverEntry *ServerEntry) bool {
	controller.tunnelMutex.Lock()
	defer controller.tunnelMutex.Unlock()
	for _, activeTunnel := range controller.tunnels {
		if activeTunnel.serverEntry.IpAddress == serverEntry.IpAddress {
			return true
		}
	}
	return false
}

// Dial selects an active tunnel and establishes a port forward
// connection through the selected tunnel. Failure to connect is considered
// a port foward failure, for the purpose of monitoring tunnel health.
func (controller *Controller) Dial(
	remoteAddr string, alwaysTunnel bool, downstreamConn net.Conn) (conn net.Conn, err error) {

	tunnel := controller.getNextActiveTunnel()
	if tunnel == nil {
		return nil, ContextError(errors.New("no active tunnels"))
	}

	// Perform split tunnel classification when feature is enabled, and if the remote
	// address is classified as untunneled, dial directly.
	if !alwaysTunnel && controller.config.SplitTunnelDnsServer != "" {

		host, _, err := net.SplitHostPort(remoteAddr)
		if err != nil {
			return nil, ContextError(err)
		}

		// Note: a possible optimization, when split tunnel is active and IsUntunneled performs
		// a DNS resolution in order to make its classification, is to reuse that IP address in
		// the following Dials so they do not need to make their own resolutions. However, the
		// way this is currently implemented ensures that, e.g., DNS geo load balancing occurs
		// relative to the outbound network.

		if splitTunnelClassifier.IsUntunneled(host) {
			// !TODO! track downstreamConn and close it when the DialTCP conn closes, as with tunnel.Dial conns?
			return DialTCP(remoteAddr, controller.untunneledDialConfig)
		}
	}

	tunneledConn, err := tunnel.Dial(remoteAddr, alwaysTunnel, downstreamConn)
	if err != nil {
		return nil, ContextError(err)
	}

	return tunneledConn, nil
}

// startEstablishing creates a pool of worker goroutines which will
// attempt to establish tunnels to candidate servers. The candidates
// are generated by another goroutine.
func (controller *Controller) startEstablishing() {
	if controller.isEstablishing {
		return
	}
	NoticeInfo("start establishing")
	controller.isEstablishing = true
	controller.establishWaitGroup = new(sync.WaitGroup)
	controller.stopEstablishingBroadcast = make(chan struct{})
	controller.candidateServerEntries = make(chan *ServerEntry)
	controller.establishPendingConns.Reset()

	for i := 0; i < controller.config.ConnectionWorkerPoolSize; i++ {
		controller.establishWaitGroup.Add(1)
		go controller.establishTunnelWorker()
	}

	controller.establishWaitGroup.Add(1)
	go controller.establishCandidateGenerator()
}

// stopEstablishing signals the establish goroutines to stop and waits
// for the group to halt. pendingConns is used to interrupt any worker
// blocked on a socket connect.
func (controller *Controller) stopEstablishing() {
	if !controller.isEstablishing {
		return
	}
	NoticeInfo("stop establishing")
	close(controller.stopEstablishingBroadcast)
	// Note: on Windows, interruptibleTCPClose doesn't really interrupt socket connects
	// and may leave goroutines running for a time after the Wait call.
	controller.establishPendingConns.CloseAll()
	// Note: establishCandidateGenerator closes controller.candidateServerEntries
	// (as it may be sending to that channel).
	controller.establishWaitGroup.Wait()

	controller.isEstablishing = false
	controller.establishWaitGroup = nil
	controller.stopEstablishingBroadcast = nil
	controller.candidateServerEntries = nil
}

// establishCandidateGenerator populates the candidate queue with server entries
// from the data store. Server entries are iterated in rank order, so that promoted
// servers with higher rank are priority candidates.
func (controller *Controller) establishCandidateGenerator() {
	defer controller.establishWaitGroup.Done()
	defer close(controller.candidateServerEntries)

	iterator, err := NewServerEntryIterator(controller.config)
	if err != nil {
		NoticeAlert("failed to iterate over candidates: %s", err)
		controller.SignalComponentFailure()
		return
	}
	defer iterator.Close()

loop:
	// Repeat until stopped
	for {

		// Send each iterator server entry to the establish workers
		startTime := time.Now()
		for {
			serverEntry, err := iterator.Next()
			if err != nil {
				NoticeAlert("failed to get next candidate: %s", err)
				controller.SignalComponentFailure()
				break loop
			}
			if serverEntry == nil {
				// Completed this iteration
				break
			}

			// TODO: here we could generate multiple candidates from the
			// server entry when there are many MeekFrontingAddresses.

			select {
			case controller.candidateServerEntries <- serverEntry:
			case <-controller.stopEstablishingBroadcast:
				break loop
			case <-controller.shutdownBroadcast:
				break loop
			}

			if time.Now().After(startTime.Add(ESTABLISH_TUNNEL_WORK_TIME_SECONDS)) {
				// Start over, after a brief pause, with a new shuffle of the server
				// entries, and potentially some newly fetched server entries.
				break
			}
		}
		// Free up resources now, but don't reset until after the pause.
		iterator.Close()

		// Trigger a fetch remote server list, since we may have failed to
		// connect with all known servers. Don't block sending signal, since
		// this signal may have already been sent.
		// Don't wait for fetch remote to succeed, since it may fail and
		// enter a retry loop and we're better off trying more known servers.
		// TODO: synchronize the fetch response, so it can be incorporated
		// into the server entry iterator as soon as available.
		select {
		case controller.signalFetchRemoteServerList <- *new(struct{}):
		default:
		}

		// After a complete iteration of candidate servers, pause before iterating again.
		// This helps avoid some busy wait loop conditions, and also allows some time for
		// network conditions to change. Also allows for fetch remote to complete,
		// in typical conditions (it isn't strictly necessary to wait for this, there will
		// be more rounds if required).
		timeout := time.After(ESTABLISH_TUNNEL_PAUSE_PERIOD)
		select {
		case <-timeout:
			// Retry iterating
		case <-controller.stopEstablishingBroadcast:
			break loop
		case <-controller.shutdownBroadcast:
			break loop
		}

		iterator.Reset()
	}

	NoticeInfo("stopped candidate generator")
}

// establishTunnelWorker pulls candidates from the candidate queue, establishes
// a connection to the tunnel server, and delivers the established tunnel to a channel.
func (controller *Controller) establishTunnelWorker() {
	defer controller.establishWaitGroup.Done()
loop:
	for serverEntry := range controller.candidateServerEntries {
		// Note: don't receive from candidateServerEntries and stopEstablishingBroadcast
		// in the same select, since we want to prioritize receiving the stop signal
		if controller.isStopEstablishingBroadcast() {
			break loop
		}

		// There may already be a tunnel to this candidate. If so, skip it.
		if controller.isActiveTunnelServerEntry(serverEntry) {
			continue
		}

		if !WaitForNetworkConnectivity(
			controller.config.NetworkConnectivityChecker,
			controller.stopEstablishingBroadcast) {
			break loop
		}

		tunnel, err := EstablishTunnel(
			controller.config,
			controller.sessionId,
			controller.establishPendingConns,
			serverEntry,
			controller) // TunnelOwner
		if err != nil {
			// Before emitting error, check if establish interrupted, in which
			// case the error is noise.
			if controller.isStopEstablishingBroadcast() {
				break loop
			}
			NoticeInfo("failed to connect to %s: %s", serverEntry.IpAddress, err)
			continue
		}

		// Deliver established tunnel.
		// Don't block. Assumes the receiver has a buffer large enough for
		// the number of desired tunnels. If there's no room, the tunnel must
		// not be required so it's discarded.
		select {
		case controller.establishedTunnels <- tunnel:
		default:
			controller.discardTunnel(tunnel)
		}
	}
	NoticeInfo("stopped establish worker")
}

func (controller *Controller) isStopEstablishingBroadcast() bool {
	select {
	case <-controller.stopEstablishingBroadcast:
		return true
	default:
	}
	return false
}
