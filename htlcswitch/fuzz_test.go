package htlcswitch

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"testing"
	"time"

	"github.com/btcsuite/btcd/btcec/v2"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/wire"
	sphinx "github.com/lightningnetwork/lightning-onion"
	"github.com/lightningnetwork/lnd/contractcourt"
	"github.com/lightningnetwork/lnd/fn/v2"
	"github.com/lightningnetwork/lnd/htlcswitch/hop"
	"github.com/lightningnetwork/lnd/invoices"
	"github.com/lightningnetwork/lnd/lntypes"
	"github.com/lightningnetwork/lnd/lnwallet"
	"github.com/lightningnetwork/lnd/lnwallet/chainfee"
	"github.com/lightningnetwork/lnd/lnwire"
	"github.com/lightningnetwork/lnd/routing/route"
	"github.com/lightningnetwork/lnd/tlv"
	"github.com/stretchr/testify/require"
)

const (
	// Channel buffer size.
	fuzzMsgChannelSize = 200

	// total number of fuzz state actions.
	numFuzzStates = 7

	// Data length required for fuzzing.
	setupDataSize    = 134
	totalHTLCAddSize = 47
	preimageSize     = 32

	// Configuration offsets.
	remoteConfigOffset = 84
	localConfigOffset  = 109

	// Fuzz state offsets.
	preimageOffset          = 15
	updateFeeOffset         = 10
	stfuStateOffset         = 3
	stateExchangeOffset     = 2
	udpateBlockHeightOffset = 5
)

// fuzzState represents the different states in the HTLC fuzz state machine.
type fuzzState uint8

// Fuzz state machine actions.
const (
	// Send an AddHTLC message.
	sendAddHTLC fuzzState = iota

	// Send a CommitSig message for outstanding HTLCs.
	sendCommitSig

	// Send a UpdateFee message to the peer.
	sendUpdateFee

	// Process the stfu state between peers (e.g., initialize stfu or resume
	// the state).
	exchangeStfu

	// Exchange protocol messages between peers (e.g., UpdateFulfill,
	// UpdateFail, RevokeAndAck).
	exchangeStateUpdates

	// Update the block height in the fuzz network, this will always
	// increase the block height based on the fuzz data.
	updateBlockHeight

	// Restart nodes.
	restartNode
)

// expectedErrors tracks which error conditions are expected due to intentional
// message malformation during fuzzing. These flags indicate that the link may
// legitimately receive and reject invalid messages.
type expectedErrors struct {
	invalidUpdate     bool
	invalidCommitment bool
	invalidRevocation bool
	invalidSync       bool
	invalidStfu       bool
	invalidUpdateFee  bool
}

// fuzzNetwork represents a test network harness used for fuzzing HTLC state
// transitions between a local and a remote peer.
type fuzzNetwork struct {
	t             *testing.T
	linkSetupData []byte
	data          []byte
	blockHeight   *uint32

	remoteRegistry     *mockInvoiceRegistry
	remoteLink         *channelLink
	remoteChannel      *testLightningChannel
	remoteExpectedErrs *expectedErrors

	localRegistry     *mockInvoiceRegistry
	localLink         *channelLink
	localChannel      *testLightningChannel
	localExpectedErrs *expectedErrors
}

// HTLCFuzzParams holds parameters for HTLC creation during fuzz testing.
type HTLCFuzzParams struct {
	attemptID      uint64
	addInvoice     bool
	isRemoteSender bool
	amount         lnwire.MilliSatoshi
	preimage       lntypes.Preimage
	hash           [32]byte
	finalCLTVDelta int32
}

// byteToFloat64 converts a byte to a float64 in range [0.1, 1.0].
func byteToFloat64(b byte) float64 {
	return 0.1 + (float64(b)/255.0)*(0.9)
}

// getUint64 extracts a uint64 from a byte slice.
func getUint64(data []byte) uint64 {
	return binary.BigEndian.Uint64(data)
}

// getUint32 extracts a uint32 from a byte slice.
func getUint32(data []byte) uint32 {
	return binary.BigEndian.Uint32(data)
}

// hasEnoughData checks if there's sufficient data remaining.
func hasEnoughData(data []byte, offset, required int) bool {
	return offset+required <= len(data)
}

// createChannelLink constructs a channelLink for fuzz testing.
func createChannelLink(t *testing.T, privKey *btcec.PrivateKey, peer *mockPeer,
	channel *lnwallet.LightningChannel, registry *mockInvoiceRegistry,
	data []byte, blockHeight *uint32) (*channelLink, *expectedErrors) {

	t.Helper()

	feeEstimator := chainfee.NewStaticEstimator(
		chainfee.SatPerKWeight(getUint64(data[0:8])),
		chainfee.SatPerKWeight(getUint64(data[8:16])),
	)

	sphinxRouter := sphinx.NewRouter(
		&sphinx.PrivKeyECDH{PrivKey: privKey},
		sphinx.NewMemoryReplayLog(),
	)
	require.NoError(t, sphinxRouter.Start())
	t.Cleanup(func() { sphinxRouter.Stop() })

	decoder := hop.NewOnionProcessor(sphinxRouter)
	pCache := newMockPreimageCache()
	expectedErrs := &expectedErrors{}

	notifyContractUpdate := func(u *contractcourt.ContractUpdate) error {
		return nil
	}

	getAliases := func(base lnwire.ShortChannelID) []lnwire.ShortChannelID {
		return nil
	}

	forwardPackets := func(linkQuit <-chan struct{}, _ bool,
		packets ...*htlcPacket) error {

		for _, packet := range packets {
			// Currently we are considering direct payments only in
			// the fuzz test, so no forwarding should happen.
			if _, ok := packet.htlc.(*lnwire.UpdateAddHTLC); ok {
				t.Fatalf("unexpected forwarded HTLC "+
					"packets: %v", packets)
			}
		}

		return nil
	}

	onChannelFailure := func(_ lnwire.ChannelID,
		_ lnwire.ShortChannelID, linkErr LinkFailureError) {

		switch linkErr.code {
		case ErrInvalidCommitment:
			require.True(t, expectedErrs.invalidCommitment)
		case ErrInvalidRevocation:
			require.True(t, expectedErrs.invalidRevocation)
		case ErrStfuViolation:
			require.True(t, expectedErrs.invalidStfu)
		case ErrInvalidUpdate:
			require.True(t, expectedErrs.invalidUpdate)
		case ErrSyncError, ErrRecoveryError:
			require.True(t, expectedErrs.invalidSync)
		case ErrInternalError:
			require.True(t, expectedErrs.invalidUpdateFee)
		default:
			t.Fatalf("received unexpected link error: %v",
				linkErr.code)
		}
	}

	bestHeight := func() uint32 { return *blockHeight }

	link := NewChannelLink(
		ChannelLinkConfig{
			BestHeight:             bestHeight,
			Peer:                   peer,
			Circuits:               &mockCircuitMap{},
			ForwardPackets:         forwardPackets,
			DecodeHopIterators:     decoder.DecodeHopIterators,
			ExtractErrorEncrypter:  decoder.ExtractErrorEncrypter,
			FetchLastChannelUpdate: mockGetChanUpdateMessage,
			Registry:               registry,
			FeeEstimator:           feeEstimator,
			PreimageCache:          pCache,
			UpdateContractSignals: func(*contractcourt.
				ContractSignals) error {

				return nil
			},
			NotifyContractUpdate: notifyContractUpdate,
			ChainEvents: &contractcourt.
				ChainEventSubscription{},
			BatchSize:           10000,
			BatchTicker:         &noopTicker{},
			FwdPkgGCTicker:      &noopTicker{},
			PendingCommitTicker: &noopTicker{},
			MinUpdateTimeout:    30 * time.Minute,
			MaxUpdateTimeout:    40 * time.Minute,
			OnChannelFailure:    onChannelFailure,
			MaxFeeAllocation:    byteToFloat64(data[16]),
			MaxFeeExposure: lnwire.MilliSatoshi(
				getUint64(data[17:25]),
			),
			NotifyActiveLink:        func(wire.OutPoint) {},
			NotifyActiveChannel:     func(wire.OutPoint) {},
			NotifyInactiveChannel:   func(wire.OutPoint) {},
			NotifyInactiveLinkEvent: func(wire.OutPoint) {},
			HtlcNotifier:            &mockHTLCNotifier{},
			GetAliases:              getAliases,
		},
		channel,
	)

	// Attach a mock mailbox.
	link.AttachMailBox(&mockMailBox{})

	channelLink, ok := link.(*channelLink)
	require.True(t, ok)

	return channelLink, expectedErrs
}

// setupSide initializes one side of invoice registry and channel link.
func setupSide(t *testing.T, privKey *btcec.PrivateKey, remotePub [33]byte,
	channel *lnwallet.LightningChannel, data []byte, blockHeight *uint32,
	syncMsg lnwire.Message) (*mockInvoiceRegistry,
	*channelLink, *expectedErrors) {

	t.Helper()
	registry := newMockRegistry(t)

	link, expectedErrors := createChannelLink(
		t, privKey, createMockPeer(remotePub), channel, registry, data,
		blockHeight,
	)

	// Forcefully share the channel_reestablish message to mark the link as
	// reestablished. If this is not done forcefully, the resumeLink
	// goroutine will block.
	link.upstream = make(chan lnwire.Message, 1)
	link.upstream <- syncMsg
	_ = link.resumeLink(t.Context())

	return registry, link, expectedErrors
}

// setupFuzzNetwork creates a two peer network for fuzz testing the HTLC state
// machine.
func setupFuzzNetwork(t *testing.T, data []byte) *fuzzNetwork {
	t.Helper()

	if !hasEnoughData(data, 0, setupDataSize) {
		return nil
	}

	_, chanID := genID()
	aliceAmount := btcutil.Amount(getUint64(data[0:8]))
	bobAmount := btcutil.Amount(getUint64(data[8:16]))
	aliceReserve := btcutil.Amount(getUint64(data[16:24]))
	bobReserve := btcutil.Amount(getUint64(data[24:32]))
	aliceDustLimit := btcutil.Amount(getUint64(data[32:40]))
	bobDustLimit := btcutil.Amount(getUint64(data[40:48]))
	aliceFeePerKw := chainfee.SatPerKWeight(getUint64(data[48:56]))
	aliceMinHTLC := lnwire.NewMSatFromSatoshis(btcutil.Amount(getUint64(
		data[56:64],
	)))
	bobMinHTLC := lnwire.NewMSatFromSatoshis(btcutil.Amount(getUint64(
		data[64:72],
	)))
	aliceFeeWu := lntypes.WeightUnit(getUint64(data[72:80]))
	blockHeight := getUint32(data[80:84])

	var remotePub, localPub [33]byte
	remoteKeyPriv, remoteKeyPub := btcec.PrivKeyFromBytes(alicePrivKey)
	localKeyPriv, localKeyPub := btcec.PrivKeyFromBytes(bobPrivKey)
	copy(remotePub[:], remoteKeyPub.SerializeCompressed())
	copy(localPub[:], localKeyPub.SerializeCompressed())

	// Create lightning channels between Local and Remote peers.
	remoteChannel, localChannel, err := createTestChannel(t, alicePrivKey,
		bobPrivKey, aliceAmount, bobAmount, aliceReserve, bobReserve,
		aliceDustLimit, bobDustLimit, aliceFeePerKw, aliceMinHTLC,
		bobMinHTLC, aliceFeeWu, chanID,
	)
	if err != nil {
		// Invalid configuration from fuzzer
		return nil
	}

	// Remote side setup.
	localChanSyncMsg, err := localChannel.channel.State().ChanSyncMsg()
	require.NoError(t, err)
	remoteRegistry, remoteLink, remoteExpectedErrs := setupSide(
		t, remoteKeyPriv, localPub, remoteChannel.channel,
		data[remoteConfigOffset:], &blockHeight, localChanSyncMsg,
	)

	// Local side setup.
	remoteChanSyncMsg, err := remoteChannel.channel.State().ChanSyncMsg()
	require.NoError(t, err)
	localRegistry, localLink, localExpectedErrs := setupSide(
		t, localKeyPriv, remotePub, localChannel.channel,
		data[localConfigOffset:], &blockHeight, remoteChanSyncMsg,
	)

	return &fuzzNetwork{
		t:             t,
		linkSetupData: data[remoteConfigOffset:setupDataSize],
		data:          data[setupDataSize:],
		blockHeight:   &blockHeight,

		remoteRegistry:     remoteRegistry,
		remoteLink:         remoteLink,
		remoteChannel:      remoteChannel,
		remoteExpectedErrs: remoteExpectedErrs,

		localRegistry:     localRegistry,
		localLink:         localLink,
		localChannel:      localChannel,
		localExpectedErrs: localExpectedErrs,
	}
}

// parseHTLCParams extracts HTLC parameters from fuzz data.
func parseHTLCParams(data []byte, offset int,
	attemptID uint64) (HTLCFuzzParams, int) {

	params := HTLCFuzzParams{
		attemptID:      attemptID,
		addInvoice:     uint64(data[offset+1])%2 > 0,
		isRemoteSender: uint64(data[offset+2])%2 > 0,
		// Set the amount/CLTV delta to be greater than 0.
		amount: lnwire.NewMSatFromSatoshis(
			max(1, btcutil.Amount(
				getUint64(data[offset+3:offset+11]),
			)),
		),
		finalCLTVDelta: max(
			1, int32(getUint32(data[offset+11:offset+15])),
		),
	}

	// Extract preimage from fuzz data.
	copy(
		params.preimage[:],
		data[offset+preimageOffset:offset+preimageOffset+preimageSize],
	)
	params.hash = sha256.Sum256(params.preimage[:])

	return params, offset + totalHTLCAddSize
}

// addInvoiceToRegistry adds an invoice to the appropriate registry.
func (network *fuzzNetwork) addInvoiceToRegistry(params HTLCFuzzParams) {
	network.t.Helper()

	invoice := invoices.Invoice{
		CreationDate: time.Now(),
		Terms: invoices.ContractTerm{
			FinalCltvDelta:  params.finalCLTVDelta,
			PaymentPreimage: &params.preimage,
			Features: lnwire.NewFeatureVector(
				nil, lnwire.Features,
			),
		},
	}

	var registry *mockInvoiceRegistry
	switch {
	case params.isRemoteSender:
		registry = network.localRegistry
	default:
		registry = network.remoteRegistry
	}

	// We will skip checking the error returned while adding the invoice to
	// the registry because there are cases where the fuzzer may generate a
	// duplicate preimage or an all-zero preimage. In such cases, the
	// invoice won't be added, so we will proceed with the payment with
	// unknown hash case.
	_ = registry.AddInvoice(network.t.Context(), invoice, params.hash)
}

// buildRoute constructs a route for the HTLC.
func (network *fuzzNetwork) buildRoute(sender, receiver *channelLink,
	amount lnwire.MilliSatoshi, timelock uint32) *route.Route {

	hop := &route.Hop{
		PubKeyBytes:      sender.PeerPubKey(),
		AmtToForward:     amount,
		OutgoingTimeLock: timelock,
	}

	return &route.Route{
		TotalTimeLock: timelock,
		TotalAmount:   amount,
		SourcePubKey:  receiver.PeerPubKey(),
		Hops:          []*route.Hop{hop},
	}
}

// generateOnionBlob creates an encoded onion packet.
func (network *fuzzNetwork) generateOnionBlob(sphinxPath *sphinx.PaymentPath,
	paymentHash [32]byte) [lnwire.OnionPacketSize]byte {

	sessionKey, err := btcec.NewPrivateKey()
	require.NoError(network.t, err)

	onionPacket, err := sphinx.NewOnionPacket(
		sphinxPath, sessionKey, paymentHash[:],
		sphinx.DeterministicPacketFiller,
	)
	require.NoError(network.t, err)

	var buffer bytes.Buffer
	err = onionPacket.Encode(&buffer)
	require.NoError(network.t, err)

	var blob [lnwire.OnionPacketSize]byte
	copy(blob[:], buffer.Bytes())

	return blob
}

// createAddHTLCFromParams creates an HTLC from fuzz parameters.
func (network *fuzzNetwork) createAddHTLCFromParams(
	params HTLCFuzzParams) *lnwire.UpdateAddHTLC {

	network.t.Helper()

	if params.addInvoice {
		network.addInvoiceToRegistry(params)
	}

	// Determine sender and receiver based on forwarding direction.
	var sender, receiver *channelLink
	if params.isRemoteSender {
		sender = network.remoteLink
		receiver = network.localLink
	} else {
		sender = network.localLink
		receiver = network.remoteLink
	}

	timeLock := *network.blockHeight + uint32(params.finalCLTVDelta)

	route := network.buildRoute(sender, receiver, params.amount, timeLock)
	sphinxPath, err := route.ToSphinxPath()
	require.NoError(network.t, err)

	blob := network.generateOnionBlob(sphinxPath, params.hash)

	return &lnwire.UpdateAddHTLC{
		PaymentHash: params.hash,
		Amount:      params.amount,
		Expiry:      timeLock,
		OnionBlob:   blob,
	}
}

// LND imposes a maximum channel buffer size of 50 for sending channel update
// messages. Once the buffer is full, additional messages must wait until buffer
// space becomes available.
//
// Therefore, before creating/sending more updates, check whether buffer space
// is available, otherwise, first exchange the pending updates.
func (network *fuzzNetwork) canCreateUpdate(link *channelLink) bool {
	network.t.Helper()

	peer, ok := link.cfg.Peer.(*mockPeer)
	require.True(network.t, ok)

	return len(peer.sentMsgs) <= 50
}

// processHTLCAdd handles the HTLC addition actions.
func (network *fuzzNetwork) processHTLCAdd(offset int, attemptID uint64) int {
	network.t.Helper()

	// Ensure we have enough data for HTLC parameters.
	if !hasEnoughData(network.data, offset, totalHTLCAddSize) {
		return len(network.data)
	}

	// Send HTLC through the appropriate link.
	var link *channelLink
	params, newOffset := parseHTLCParams(network.data, offset, attemptID)
	if params.isRemoteSender {
		link = network.remoteLink
	} else {
		link = network.localLink

		// If the local link has failed, it will not create any further
		// updates.
		if link.failed {
			return newOffset
		}
	}

	if !network.canCreateUpdate(link) {
		return newOffset
	}

	htlc := network.createAddHTLCFromParams(params)

	packet := &htlcPacket{
		incomingChanID: hop.Source,
		incomingHTLCID: params.attemptID,
		outgoingChanID: link.ShortChanID(),
		htlc:           htlc,
		amount:         htlc.Amount,
	}
	circuit := newPaymentCircuit(&htlc.PaymentHash, packet)
	packet.circuit = circuit

	// If adding this HTLC would exceed the maximum fee exposure or would
	// cause our channel balance or the peer's channel balance to fall below
	// the channel reserve requirement, the HTLC addition will fail. So we
	// will not add further HTLCs.
	_ = link.handleDownstreamUpdateAdd(network.t.Context(), packet)

	// Here, we could receive a link failure because the given htlc might
	// cause dust to exceed the configured fee limit.
	if params.isRemoteSender {
		network.localExpectedErrs.invalidUpdateFee = true
	} else {
		network.remoteExpectedErrs.invalidUpdateFee = true
	}

	return newOffset
}

// processCommitSig handles sending a CommitSig message to the peer.
func (network *fuzzNetwork) processCommitSig(offset int) int {
	network.t.Helper()

	// Ensure we have enough data for CommitSignatures.
	if !hasEnoughData(network.data, offset, stateExchangeOffset) {
		return len(network.data)
	}

	isRemoteSender := uint64(network.data[offset+1])%2 > 0
	var sender *channelLink

	if isRemoteSender {
		sender = network.remoteLink
	} else {
		sender = network.localLink

		// If the local link has failed, it will not create any further
		// updates.
		if sender.failed {
			return offset + stateExchangeOffset
		}
	}

	if !network.canCreateUpdate(sender) {
		return offset + stateExchangeOffset
	}

	// Send the commit_sig message only if there are pending commitment
	// update messages on the sender side, or if the sender is the remote
	// node.
	pending := sender.channel.NumPendingUpdates(
		lntypes.Local, lntypes.Remote,
	)
	if pending > 0 || isRemoteSender {
		_ = sender.updateCommitTx(network.t.Context())
	}

	return offset + stateExchangeOffset
}

// processUpdateFee handles sending a UpdateFee message to the peer.
func (network *fuzzNetwork) processUpdateFee(offset int) int {
	network.t.Helper()

	// Ensure we have enough data for UpdateFee.
	if !hasEnoughData(network.data, offset, updateFeeOffset) {
		return len(network.data)
	}

	isRemoteSender := uint64(network.data[offset+1])%2 > 0
	var sender *channelLink

	if isRemoteSender {
		sender = network.remoteLink
	} else {
		sender = network.localLink

		// If the local link has failed, it will not create any further
		// updates.
		if sender.failed {
			return offset + stateExchangeOffset
		}
	}

	if !network.canCreateUpdate(sender) {
		return offset + stateExchangeOffset
	}

	_ = sender.updateChannelFee(
		network.t.Context(), chainfee.SatPerKWeight(
			btcutil.Amount(getUint64(
				network.data[offset+2:offset+10],
			)),
		),
	)

	// Here, we could receive a link failure because the given fee might
	// cause dust to exceed the configured fee limit.
	if isRemoteSender {
		network.localExpectedErrs.invalidUpdateFee = true
	} else {
		network.remoteExpectedErrs.invalidUpdateFee = true
	}

	return offset + updateFeeOffset
}

// processStfu drives the quiescence (stfu) state transition for a channel link.
func (network *fuzzNetwork) processStfu(offset int) int {
	network.t.Helper()

	// Ensure we have enough data to drive the stfu transition.
	if !hasEnoughData(network.data, offset, stfuStateOffset) {
		return len(network.data)
	}

	isRemoteSender := uint64(network.data[offset+1])%2 > 0
	var node *channelLink

	if isRemoteSender {
		node = network.remoteLink
	} else {
		node = network.localLink

		// If the local link has failed, it will not create any further
		// updates.
		if node.failed {
			return offset + stateExchangeOffset
		}
	}

	if !network.canCreateUpdate(node) {
		return offset + stateExchangeOffset
	}

	switch network.data[offset+2] % 3 {
	case 0:
		// Send the stfu message.
		req, _ := fn.NewReq[fn.Unit, fn.Result[lntypes.ChannelParty]](
			fn.Unit{},
		)
		_ = node.handleQuiescenceReq(req)
	case 1:
		if isRemoteSender {
			// remote sender will send the stfu anyway.
			stfu := &lnwire.Stfu{
				ChanID:    node.ChanID(),
				Initiator: (network.data[offset+2] % 2) == 0,
			}
			_ = network.remoteLink.cfg.Peer.SendMessage(false, stfu)
		}
	default:
		// Stop the quiescence state.
		node.quiescer.Resume()
	}

	// Local can experience a link failure if the remote sends an invalid
	// stfu message.
	//
	// Remote can also experience errors if it forcefully sends an stfu
	// message to the peer and then receives an stfu reply back, which the
	// remote was not expecting.
	//
	// Either of them may experience a link failure if they send the stfu,
	// but then resume their state before receiving the stfu update from the
	// peer.
	//
	// Because of this, the link can fail on the remote side, but we will
	// ignore the link failure on the remote side and still proceed (in a
	// real scenario, the remote link can be restarted to fix the issue).
	network.localExpectedErrs.invalidStfu = true
	network.remoteExpectedErrs.invalidStfu = true

	return offset + stfuStateOffset
}

// maybeMalformMessage conditionally mutates an lnwire message using
// fuzzing input data. Mutation is applied only for messages received from a
// remote peer and only when the initial selector byte allows it.
//
// Fuzz data is consumed sequentially starting from offset. Each field mutation
// uses its own selector byte. If insufficient data is available for a field,
// that field is left unchanged while others may still be mutated.
func (network *fuzzNetwork) maybeMalformMessage(msg lnwire.Message, offset int,
	isRemoteSender bool) (lnwire.Message, int) {

	network.t.Helper()

	if !isRemoteSender || offset >= len(network.data) {
		return msg, offset
	}

	// Global selector.
	cursor := offset
	// skip malformation for even selector bytes.
	if network.data[cursor]%2 == 0 {
		return msg, cursor + 1
	}
	cursor++

	canMutate := func(n int, useSelector bool) bool {
		if !hasEnoughData(network.data, cursor, n) {
			return false
		}

		// If we don't want to consume a selector byte, mutation is
		// allowed.
		if !useSelector {
			return true
		}

		allowed := (network.data[cursor] % 2) == 0
		cursor++

		return allowed
	}

	switch m := msg.(type) {
	case *lnwire.UpdateAddHTLC:
		out := *m

		// ID
		if canMutate(9, true) {
			out.ID = getUint64(network.data[cursor : cursor+8])
			cursor += 8
			network.localExpectedErrs.invalidUpdate = true
		}

		// Amount
		if canMutate(9, true) {
			out.Amount = lnwire.NewMSatFromSatoshis(
				btcutil.Amount(getUint64(
					network.data[cursor : cursor+8],
				)),
			)
			cursor += 8
			network.localExpectedErrs.invalidUpdate = true
		}

		// Expiry
		if canMutate(5, true) {
			out.Expiry = getUint32(network.data[cursor : cursor+4])
			cursor += 4
			network.localExpectedErrs.invalidUpdate = true
		}

		// OnionBlob
		if canMutate(1367, true) {
			copy(out.OnionBlob[:], network.data[cursor:cursor+1366])
			cursor += 1366
			network.localExpectedErrs.invalidUpdate = true
		}

		// BlindingPoint
		if canMutate(34, true) {
			blinding, err := btcec.ParsePubKey(
				network.data[cursor : cursor+33],
			)

			// Only modify if the pubkey bytes are correct.
			if err == nil {
				out.BlindingPoint = tlv.SomeRecordT(
					tlv.NewPrimitiveRecord[lnwire.
						BlindingPointTlvType](blinding),
				)
				network.localExpectedErrs.invalidUpdate = true
			}
			cursor += 33
		}

		return &out, cursor

	case *lnwire.UpdateFulfillHTLC:
		out := *m

		// ID
		if canMutate(9, true) {
			out.ID = getUint64(network.data[cursor : cursor+8])
			cursor += 8
			network.localExpectedErrs.invalidUpdate = true
		}

		// PaymentPreimage
		if canMutate(33, true) {
			copy(
				out.PaymentPreimage[:],
				network.data[cursor:cursor+32],
			)
			cursor += 32
			network.localExpectedErrs.invalidUpdate = true
		}

		return &out, cursor

	case *lnwire.UpdateFailMalformedHTLC:
		out := *m

		// ID
		if canMutate(9, true) {
			out.ID = getUint64(network.data[cursor : cursor+8])
			cursor += 8
			network.localExpectedErrs.invalidUpdate = true
		}

		// FailureCode
		if canMutate(3, true) {
			out.FailureCode = lnwire.FailCode(
				binary.BigEndian.Uint16(
					network.data[cursor : cursor+2],
				),
			)
			cursor += 2
			network.localExpectedErrs.invalidUpdate = true
		}

		// ShaOnionBlob
		if canMutate(33, true) {
			copy(
				out.ShaOnionBlob[:],
				network.data[cursor:cursor+32],
			)
			cursor += 32
			network.localExpectedErrs.invalidUpdate = true
		}

		return &out, cursor

	case *lnwire.UpdateFailHTLC:
		out := *m

		// ID
		if canMutate(9, true) {
			out.ID = getUint64(network.data[cursor : cursor+8])
			cursor += 8
			network.localExpectedErrs.invalidUpdate = true
		}

		// Reason
		if canMutate(3, true) {
			length := int(binary.BigEndian.Uint16(
				network.data[cursor : cursor+2],
			))
			cursor += 2

			if canMutate(length, false) {
				out.Reason = lnwire.OpaqueReason(
					network.data[cursor : cursor+length],
				)
				cursor += length
				network.localExpectedErrs.invalidUpdate = true
			}
		}

		return &out, cursor

	case *lnwire.CommitSig:
		out := *m

		// CommitSig
		if canMutate(65, true) {
			if sig, err := lnwire.NewSigFromWireECDSA(
				network.data[cursor : cursor+64],
			); err == nil {
				out.CommitSig = sig
				network.localExpectedErrs.
					invalidCommitment = true
			}
			cursor += 64
		}

		// HTLC sigs
		var htlcSigs []lnwire.Sig
		for _, sig := range out.HtlcSigs {
			if canMutate(65, true) {
				if newSig, err := lnwire.NewSigFromWireECDSA(
					network.data[cursor : cursor+64],
				); err == nil {
					htlcSigs = append(htlcSigs, newSig)
					network.localExpectedErrs.
						invalidCommitment = true
				}
				cursor += 64

				if canMutate(1, true) {
					htlcSigs = append(htlcSigs, sig)
				}
			} else {
				htlcSigs = append(htlcSigs, sig)
			}
		}
		out.HtlcSigs = htlcSigs

		return &out, cursor

	case *lnwire.RevokeAndAck:
		out := *m

		// Revocation
		if canMutate(33, true) {
			copy(out.Revocation[:], network.data[cursor:cursor+32])
			cursor += 32
			network.localExpectedErrs.invalidRevocation = true
		}

		// NextRevocationKey
		if canMutate(34, true) {
			revocationKey, err := btcec.ParsePubKey(
				network.data[cursor : cursor+33],
			)

			// Only modify if the pubkey bytes are correct.
			if err == nil {
				out.NextRevocationKey = revocationKey
				network.localExpectedErrs.
					invalidRevocation = true
			}
			cursor += 33
		}

		return &out, cursor

	case *lnwire.UpdateFee:
		out := *m

		// FeePerKw
		if canMutate(9, true) {
			out.FeePerKw = uint32(chainfee.SatPerKWeight(
				btcutil.Amount(getUint64(
					network.data[cursor : cursor+8],
				)),
			))
			cursor += 8
			network.localExpectedErrs.invalidUpdate = true
		}

		return &out, cursor

	case *lnwire.ChannelReestablish:
		out := *m

		// NextLocalCommitHeight
		if canMutate(9, true) {
			out.NextLocalCommitHeight = getUint64(
				network.data[cursor : cursor+8],
			)
			cursor += 8
			network.localExpectedErrs.invalidSync = true
		}

		// RemoteCommitTailHeight
		if canMutate(9, true) {
			out.RemoteCommitTailHeight = getUint64(
				network.data[cursor : cursor+8],
			)
			cursor += 8
			network.localExpectedErrs.invalidSync = true
		}

		// LastRemoteCommitSecret
		if canMutate(33, true) {
			copy(
				out.LastRemoteCommitSecret[:],
				network.data[cursor:cursor+32],
			)
			cursor += 32
			network.localExpectedErrs.invalidSync = true
		}

		// LocalUnrevokedCommitPoint
		if canMutate(34, true) {
			localUnRevokedCommitPt, err := btcec.ParsePubKey(
				network.data[cursor : cursor+33],
			)

			// Only modify if the pubkey bytes are correct.
			if err == nil {
				out.LocalUnrevokedCommitPoint =
					localUnRevokedCommitPt
				network.localExpectedErrs.invalidSync = true
			}
			cursor += 33
		}

		return &out, cursor

	default:
		return msg, cursor
	}
}

// maybeReorderMessages conditionally reorder outbound messages from the remote
// peer using fuzz input data.
func (network *fuzzNetwork) maybeReorderMessages(offset int) int {
	network.t.Helper()

	// Ensure we have enough fuzz data to drive message reordering.
	if !hasEnoughData(network.data, offset, 2) {
		return len(network.data)
	}

	// skip reordering for even selector bytes.
	if network.data[offset]%2 == 0 {
		return offset + 1
	}
	offset++

	// Reordering is applied only to messages sent by the remote peer.
	peer, ok := network.remoteLink.cfg.Peer.(*mockPeer)
	require.True(network.t, ok)
	sentMsgs := peer.sentMsgs

	var msgs []lnwire.Message
readLoop:
	for {
		select {
		case msg := <-sentMsgs:
			msgs = append(msgs, msg)
		default:
			break readLoop
		}
	}

	// Swap two messages using fuzz data.
	for i := len(msgs) - 1; i > 0; i-- {
		if !hasEnoughData(network.data, offset, 1) {
			break
		}
		j := int(network.data[offset]) % (i + 1)
		msgs[i], msgs[j] = msgs[j], msgs[i]
		offset++
	}

	// Re-inject all messages in their new order.
	for _, msg := range msgs {
		_ = network.remoteLink.cfg.Peer.SendMessage(false, msg)
	}

	// Reordering can cause the CommitSig/RevokeAndAck message to be
	// considered malformed.
	network.localExpectedErrs.invalidCommitment = true
	network.localExpectedErrs.invalidRevocation = true

	return offset
}

// exchangeUpdates handles message sending between peers.
func (network *fuzzNetwork) exchangeUpdates(offset int) int {
	network.t.Helper()

	// Ensure we have enough data for exchanging updates.
	if !hasEnoughData(network.data, offset, stateExchangeOffset) {
		return len(network.data)
	}

	isRemoteSender := uint64(network.data[offset+1])%2 > 0
	var sender, receiver *channelLink
	offset += stateExchangeOffset

	if isRemoteSender {
		sender = network.remoteLink
		receiver = network.localLink

		// If the remote peer is sending a message to the local peer, we
		// may conditionally reorder the message.
		offset = network.maybeReorderMessages(offset)
	} else {
		sender = network.localLink
		receiver = network.remoteLink
	}

	peer, ok := sender.cfg.Peer.(*mockPeer)
	require.True(network.t, ok)
	sentMsgs := peer.sentMsgs

	select {
	case msg := <-sentMsgs:
		// We conditionally malform the message when the remote peer
		// is sending a message to the local peer.
		mayBeMalformedMsg, cursor := network.maybeMalformMessage(
			msg, offset, isRemoteSender,
		)

		receiver.handleUpstreamMsg(
			network.t.Context(), mayBeMalformedMsg,
		)

		offset = cursor
	default:
		// No message to send.
	}

	return offset
}

// restartNode initiates the restart of the channel and channel links. If a peer
// restarts, the channel link on both sides is stopped and then restarted
// again to handle the synchronization process.
func (network *fuzzNetwork) restartNode(offset int) int {
	network.t.Helper()
	offset++

	remoteKeyPriv, remoteKeyPub := btcec.PrivKeyFromBytes(alicePrivKey)
	localKeyPriv, localKeyPub := btcec.PrivKeyFromBytes(bobPrivKey)

	var remotePub, localPub [33]byte
	copy(remotePub[:], remoteKeyPub.SerializeCompressed())
	copy(localPub[:], localKeyPub.SerializeCompressed())

	// Restore LN channel on both sides.
	remoteChannel, err := network.remoteChannel.restore()
	require.NoError(network.t, err)
	localChannel, err := network.localChannel.restore()
	require.NoError(network.t, err)

	// Remote side setup.
	localChanSyncMsg, err := localChannel.State().ChanSyncMsg()
	require.NoError(network.t, err)
	remoteRegistry, remoteLink, remoteExpectedErrs := setupSide(
		network.t, remoteKeyPriv, localPub, remoteChannel,
		network.linkSetupData, network.blockHeight,
		localChanSyncMsg,
	)

	// Local side setup.
	remoteChanSyncMsg, err := remoteChannel.State().ChanSyncMsg()
	require.NoError(network.t, err)
	malformedMsg, cursor := network.maybeMalformMessage(
		remoteChanSyncMsg, offset, true,
	)
	localRegistry, localLink, localExpectedErrs := setupSide(
		network.t, localKeyPriv, remotePub, localChannel,
		network.linkSetupData[localConfigOffset-remoteConfigOffset:],
		network.blockHeight, malformedMsg,
	)

	network.remoteChannel.channel = remoteChannel
	network.remoteRegistry = remoteRegistry
	network.remoteLink = remoteLink
	network.remoteExpectedErrs = remoteExpectedErrs

	network.localChannel.channel = localChannel
	network.localRegistry = localRegistry
	network.localLink = localLink
	network.localExpectedErrs = localExpectedErrs

	return cursor
}

// udpateBlockHeight updates the best known block height in the fuzz network.
// The new height is selected from the fuzz data and is guaranteed to be
// monotonically increasing.
func (network *fuzzNetwork) udpateBlockHeight(offset int) int {
	network.t.Helper()

	// Ensure we have enough data for updating block height.
	if !hasEnoughData(network.data, offset, udpateBlockHeightOffset) {
		return len(network.data)
	}

	*network.blockHeight = max(
		getUint32(network.data[offset+1:offset+5]),
		*network.blockHeight,
	)

	return offset + udpateBlockHeightOffset
}

// checkChannelInvariants verifies that the channel state is consistent between
// local and remote peers.
func (network *fuzzNetwork) checkChannelInvariants() {
	network.t.Helper()

	localChan := network.localLink.channel
	remoteChan := network.remoteLink.channel
	localCommit := localChan.State().LocalCommitment
	remoteCommit := remoteChan.State().LocalCommitment

	// Check total balances.
	var localHtlcAmt, remoteHtlcAmt lnwire.MilliSatoshi
	localTotal := localCommit.LocalBalance + localCommit.RemoteBalance +
		lnwire.NewMSatFromSatoshis(localCommit.CommitFee)
	remoteTotal := remoteCommit.LocalBalance + remoteCommit.RemoteBalance +
		lnwire.NewMSatFromSatoshis(remoteCommit.CommitFee)

	for _, htlc := range localCommit.Htlcs {
		localHtlcAmt += htlc.Amt
	}
	for _, htlc := range remoteCommit.Htlcs {
		remoteHtlcAmt += htlc.Amt
	}

	require.Equal(
		network.t, localTotal+localHtlcAmt,
		lnwire.NewMSatFromSatoshis(localChan.Capacity),
	)
	require.Equal(
		network.t, remoteTotal+remoteHtlcAmt,
		lnwire.NewMSatFromSatoshis(remoteChan.Capacity),
	)

	// Check commitment heights.
	require.InDelta(
		network.t, localCommit.CommitHeight,
		remoteChan.State().RemoteCommitment.CommitHeight, 1,
	)
	require.InDelta(
		network.t, remoteCommit.CommitHeight,
		localChan.State().RemoteCommitment.CommitHeight, 1,
	)
}

// drainMessages processes all pending messages. Here, all pending messages
// are processed directly, without any malformation or further message
// reordering.
func (network *fuzzNetwork) drainMessages() {
	network.t.Helper()

	remotePeer, ok := network.remoteLink.cfg.Peer.(*mockPeer)
	require.True(network.t, ok)

	localPeer, ok := network.localLink.cfg.Peer.(*mockPeer)
	require.True(network.t, ok)

	for {
		select {
		case localMsg := <-localPeer.sentMsgs:
			network.remoteLink.handleUpstreamMsg(
				network.t.Context(), localMsg,
			)

		case remoteMsg := <-remotePeer.sentMsgs:
			network.localLink.handleUpstreamMsg(
				network.t.Context(), remoteMsg,
			)

		default:
			return
		}

		network.checkChannelInvariants()
	}
}

// runHTLCFuzzStateMachine executes the HTLC state machine with fuzz input data.
func (network *fuzzNetwork) runHTLCFuzzStateMachine() {
	network.t.Helper()

	htlcID := uint64(0)
	isLastRestarted := false

	for offset := 0; offset < len(network.data); {
		// Extract action from current data byte
		action := fuzzState(int(network.data[offset]) % numFuzzStates)

		switch action {
		case sendAddHTLC:
			offset = network.processHTLCAdd(offset, htlcID)
			htlcID++

		case sendCommitSig:
			offset = network.processCommitSig(offset)

		case sendUpdateFee:
			offset = network.processUpdateFee(offset)

		case exchangeStfu:
			offset = network.processStfu(offset)

		case exchangeStateUpdates:
			offset = network.exchangeUpdates(offset)
			isLastRestarted = false

		case updateBlockHeight:
			offset = network.udpateBlockHeight(offset)

		case restartNode:
			// Only restart the node if some message exchange has
			// happened between peers, otherwise, there is no point
			// in restarting the node again and again, as that will
			// only increase the fuzzing time.
			if !isLastRestarted {
				offset = network.restartNode(offset)
				isLastRestarted = true
			} else {
				offset++
			}
		}

		network.checkChannelInvariants()
	}

	network.drainMessages()
}

// FuzzHTLCStates fuzz-tests the HTLC state machine. It gets the input data and
// performs operations such as add, revoke, commit, fulfill, or fail  etc.
// Message exchange is controlled using mock peer instances so we can precisely
// manage transport-layer messaging and uncover edge cases.
func FuzzHTLCStates(f *testing.F) {
	// Adding appropriate htlc state machine seed inputs.
	addRemoteFulfillSeed(f)
	addLocalFailSeed(f)
	addRemoteMalformedSeed(f)

	f.Fuzz(func(t *testing.T, data []byte) {
		network := setupFuzzNetwork(t, data)

		if network != nil {
			// Execute the HTLC state machine with fuzz input.
			network.runHTLCFuzzStateMachine()
		}
	})
}

// buildHTLCFuzzSetup builds the base channel, link, and HTLC setup data used by
// the fuzz seeds.
func buildHTLCFuzzSetup() ([]byte, []byte, []byte, []byte) {
	// Preimage.
	preimage := make([]byte, preimageSize)
	for i := range preimageSize {
		preimage[i] = byte(i)
	}

	// Channel setup data.
	data := make([]byte, setupDataSize)

	// Channel Configuration.
	binary.BigEndian.PutUint64(data[0:8], 50*btcutil.SatoshiPerBitcoin)
	binary.BigEndian.PutUint64(data[8:16], 50*btcutil.SatoshiPerBitcoin)
	binary.BigEndian.PutUint64(data[16:24], 0)
	binary.BigEndian.PutUint64(data[24:32], 0)
	binary.BigEndian.PutUint64(data[32:40], 200)
	binary.BigEndian.PutUint64(data[40:48], 800)
	binary.BigEndian.PutUint64(data[48:56], 6000)
	binary.BigEndian.PutUint64(data[56:64], 0)
	binary.BigEndian.PutUint64(data[64:72], 0)
	binary.BigEndian.PutUint64(data[72:80], 724)
	binary.BigEndian.PutUint32(data[80:84], 100)

	// Remote Link.
	binary.BigEndian.PutUint64(data[84:92], 10)
	binary.BigEndian.PutUint64(data[92:100], 0)
	data[100] = 114
	binary.BigEndian.PutUint64(data[101:109], 500000000)

	// Local Link.
	binary.BigEndian.PutUint64(data[109:117], 10)
	binary.BigEndian.PutUint64(data[117:125], 0)
	data[125] = 114
	binary.BigEndian.PutUint64(data[126:134], 500000000)

	// HTLC parameters.
	htlcAmt := make([]byte, 8)
	cltvDelta := make([]byte, 4)
	binary.BigEndian.PutUint64(htlcAmt, 1)
	binary.BigEndian.PutUint32(cltvDelta, 5)

	return data, preimage, htlcAmt, cltvDelta
}

// addRemoteFulfillSeed adds a fuzz seed that simulates a Remote-to-Local HTLC
// fulfill flow.
func addRemoteFulfillSeed(f *testing.F) {
	data, preimage, htlcAmt, cltvDelta := buildHTLCFuzzSetup()
	remoteFulfill := make([]byte, 0)

	// Base setup.
	remoteFulfill = append(remoteFulfill, data...)

	// Add HTLC.
	remoteFulfill = append(remoteFulfill, byte(sendAddHTLC), 1, 1)
	remoteFulfill = append(remoteFulfill, htlcAmt...)
	remoteFulfill = append(remoteFulfill, cltvDelta...)
	remoteFulfill = append(remoteFulfill, preimage...)

	// State transitions.
	remoteFulfill = append(remoteFulfill,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(sendCommitSig), 1,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(exchangeStateUpdates), 0,
		byte(sendCommitSig), 0,
		byte(exchangeStateUpdates), 0,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(exchangeStateUpdates), 0,
		byte(sendCommitSig), 0,
		byte(exchangeStateUpdates), 0,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(sendCommitSig), 1,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(exchangeStateUpdates), 0,
	)

	f.Add(remoteFulfill)
}

// addLocalFailSeed adds a fuzz seed that simulates a Local-to-Remote HTLC fail
// flow.
func addLocalFailSeed(f *testing.F) {
	data, preimage, htlcAmt, cltvDelta := buildHTLCFuzzSetup()
	localFail := make([]byte, 0)

	// Base setup.
	localFail = append(localFail, data...)

	// Add HTLC.
	localFail = append(localFail, byte(sendAddHTLC), 0, 0)
	localFail = append(localFail, htlcAmt...)
	localFail = append(localFail, cltvDelta...)
	localFail = append(localFail, preimage...)

	// State transitions.
	localFail = append(localFail,
		byte(exchangeStateUpdates), 0,
		byte(sendCommitSig), 0,
		byte(exchangeStateUpdates), 0,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(sendCommitSig), 1,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(exchangeStateUpdates), 0,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(sendCommitSig), 1,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(exchangeStateUpdates), 0,
		byte(sendCommitSig), 0,
		byte(exchangeStateUpdates), 0,
		byte(exchangeStateUpdates), 1, 0, 0,
	)

	f.Add(localFail)
}

// addRemoteMalformedSeed adds a fuzz seed that simulates a Remote-to-Local
// HTLC fail malformed flow.
func addRemoteMalformedSeed(f *testing.F) {
	data, preimage, htlcAmt, cltvDelta := buildHTLCFuzzSetup()
	malformedBlob := make([]byte, 1366)
	remoteMalformed := make([]byte, 0)

	// Base setup.
	remoteMalformed = append(remoteMalformed, data...)

	// Add HTLC.
	remoteMalformed = append(remoteMalformed, byte(sendAddHTLC), 1, 1)
	remoteMalformed = append(remoteMalformed, htlcAmt...)
	remoteMalformed = append(remoteMalformed, cltvDelta...)
	remoteMalformed = append(remoteMalformed, preimage...)

	// State transitions.
	remoteMalformed = append(remoteMalformed,
		byte(exchangeStateUpdates), 1, 0, 1, 1, 1, 1, 0,
	)
	remoteMalformed = append(remoteMalformed, malformedBlob...)
	remoteMalformed = append(remoteMalformed, 1)
	remoteMalformed = append(remoteMalformed,
		byte(sendCommitSig), 1,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(exchangeStateUpdates), 0,
		byte(sendCommitSig), 0,
		byte(exchangeStateUpdates), 0,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(exchangeStateUpdates), 0,
		byte(sendCommitSig), 0,
		byte(exchangeStateUpdates), 0,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(sendCommitSig), 1,
		byte(exchangeStateUpdates), 1, 0, 0,
		byte(exchangeStateUpdates), 0,
	)

	f.Add(remoteMalformed)
}
