package htlcswitch

import (
	"crypto/sha256"
	"encoding/binary"
	"testing"
	"time"

	"github.com/btcsuite/btcd/btcec/v2"
	"github.com/btcsuite/btcd/btcutil"
	"github.com/btcsuite/btcd/wire"
	"github.com/lightningnetwork/lnd/contractcourt"
	"github.com/lightningnetwork/lnd/fn/v2"
	"github.com/lightningnetwork/lnd/graph/db/models"
	"github.com/lightningnetwork/lnd/htlcswitch/hop"
	"github.com/lightningnetwork/lnd/invoices"
	"github.com/lightningnetwork/lnd/lntypes"
	"github.com/lightningnetwork/lnd/lnwallet"
	"github.com/lightningnetwork/lnd/lnwallet/chainfee"
	"github.com/lightningnetwork/lnd/lnwire"
	"github.com/stretchr/testify/require"
)

const (
	// fuzzMsgChannelSize defines the channel buffer size for mock peer
	// messages.
	fuzzMsgChannelSize = 200

	// preimageSize defines the size of payment preimage in bytes.
	preimageSize = 32

	// preimageOffset defines the offset in data where preimage starts.
	preimageOffset = 4

	// stateExchangeOffset defines the offset in data where state exchange
	// ends.
	stateExchangeOffset = 2

	// updateFeeOffset defines the offset in data where update fee state
	// ends.
	updateFeeOffset = 3

	// stfuStateOffset defines the offset in data where update stfu state
	// ends.
	stfuStateOffset = 3

	// reorderMsgOffset defines the offset in data where reorder messages
	// state ends.
	reorderMsgOffset = 2

	// totalHTLCAddBytes defines total bytes consumed for HTLC add data.
	totalHTLCAddBytes = 36

	// numFuzzStates defines the total number of fuzz state actions.
	numFuzzStates = 5
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
)

// fuzzNetwork represents a test-only network harness used for fuzzing HTLC
// state transitions between a local and a remote peer. It encapsulates the
// corresponding channel links and invoice registries, and carries the fuzz
// input data consumed to drive state mutations during testing.
type fuzzNetwork struct {
	t    *testing.T
	data []byte

	remoteRegistry *mockInvoiceRegistry
	remoteLink     *channelLink

	localRegistry *mockInvoiceRegistry
	localLink     *channelLink
}

// createChannelLink constructs a channelLink instance tailored for fuzz
// testing. A variety of subsystems are mocked so the link interacts only with
// controlled, deterministic resources.
// This function is directly taken from test_utils.go with slight modifications
// to suit the fuzz test requirements.
func createChannelLink(t *testing.T, peer *mockPeer,
	channel *lnwallet.LightningChannel,
	registry *mockInvoiceRegistry) *channelLink {

	t.Helper()

	const (
		minFeeUpdateTimeout = 30 * time.Minute
		maxFeeUpdateTimeout = 40 * time.Minute
		defaultDelta        = uint32(6)
	)

	globalPolicy := models.ForwardingPolicy{
		MinHTLCOut:    lnwire.NewMSatFromSatoshis(5),
		BaseFee:       lnwire.NewMSatFromSatoshis(1),
		TimeLockDelta: defaultDelta,
	}

	obfuscator := NewMockObfuscator()
	feeEstimator := newMockFeeEstimator()
	decoder := newMockIteratorDecoder()
	pCache := newMockPreimageCache()

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

		// Do not take any action if the link fails, as this may occur
		// when the remote peer sends a malformed message to the local
		// peer. Such failures are ignored and the test continues.
	}

	bestHeight := func() uint32 { return testStartingHeight }

	link := NewChannelLink(
		ChannelLinkConfig{
			BestHeight:         bestHeight,
			FwrdingPolicy:      globalPolicy,
			Peer:               peer,
			Circuits:           &mockCircuitMap{},
			ForwardPackets:     forwardPackets,
			DecodeHopIterators: decoder.DecodeHopIterators,
			ExtractErrorEncrypter: func(*btcec.PublicKey) (
				hop.ErrorEncrypter, lnwire.FailCode) {

				return obfuscator, lnwire.CodeNone
			},
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
			BatchSize:               10000,
			BatchTicker:             &noopTicker{},
			FwdPkgGCTicker:          &noopTicker{},
			PendingCommitTicker:     &noopTicker{},
			MinUpdateTimeout:        minFeeUpdateTimeout,
			MaxUpdateTimeout:        maxFeeUpdateTimeout,
			OnChannelFailure:        onChannelFailure,
			OutgoingCltvRejectDelta: 3,
			MaxOutgoingCltvExpiry:   DefaultMaxOutgoingCltvExpiry,
			MaxFeeAllocation:        DefaultMaxLinkFeeAllocation,
			MaxFeeExposure:          DefaultMaxFeeExposure,
			MaxAnchorsCommitFeeRate: chainfee.SatPerKVByte(
				10 * 1000,
			).FeePerKWeight(),
			NotifyActiveLink:        func(wire.OutPoint) {},
			NotifyActiveChannel:     func(wire.OutPoint) {},
			NotifyInactiveChannel:   func(wire.OutPoint) {},
			NotifyInactiveLinkEvent: func(wire.OutPoint) {},
			HtlcNotifier:            &mockHTLCNotifier{},
			GetAliases:              getAliases,
			ShouldFwdExpEndorsement: func() bool { return true },
		},
		channel,
	)

	// Attach a mock mailbox.
	link.AttachMailBox(&mockMailBox{})

	channelLink, ok := link.(*channelLink)
	require.True(t, ok)

	return channelLink
}

// setupFuzzNetwork creates and initializes a simplified two-peer (local and
// remote) network environment for fuzz testing the HTLC state machine.
func setupFuzzNetwork(t *testing.T, data []byte) *fuzzNetwork {
	t.Helper()

	_, chanID := genID()
	aliceAmount := btcutil.Amount(50 * btcutil.SatoshiPerBitcoin)
	bobAmount := btcutil.Amount(50 * btcutil.SatoshiPerBitcoin)

	_, remoteKeyPub := btcec.PrivKeyFromBytes(alicePrivKey)
	_, localKeyPub := btcec.PrivKeyFromBytes(bobPrivKey)

	var remotePub [33]byte
	copy(remotePub[:], remoteKeyPub.SerializeCompressed())

	var localPub [33]byte
	copy(localPub[:], localKeyPub.SerializeCompressed())

	// Create lightning channels between Local and Remote peers.
	remoteChannel, localChannel, err := createTestChannel(t, alicePrivKey,
		bobPrivKey, aliceAmount, bobAmount, 0, 0, chanID,
	)
	require.NoError(t, err)

	// Helper closure to initialize invoice registry and channel link.
	setupSide := func(remotePub [33]byte,
		channel *lnwallet.LightningChannel) (*mockInvoiceRegistry,
		*channelLink) {

		registry := newMockRegistry(t)

		link := createChannelLink(
			t, createMockPeer(remotePub), channel, registry,
		)

		return registry, link
	}

	// Remote side setup.
	remoteRegistry, remoteLink := setupSide(localPub, remoteChannel.channel)
	remoteLink.markReestablished()

	// Local side setup.
	localRegistry, localLink := setupSide(remotePub, localChannel.channel)
	localLink.markReestablished()

	return &fuzzNetwork{
		t:    t,
		data: data,

		remoteRegistry: remoteRegistry,
		remoteLink:     remoteLink,

		localRegistry: localRegistry,
		localLink:     localLink,
	}
}

// HTLCFuzzParams holds parameters for HTLC creation during fuzz testing.
type HTLCFuzzParams struct {
	attemptID      uint64
	addInvoice     bool
	isRemoteSender bool
	amount         lnwire.MilliSatoshi
	preimage       lntypes.Preimage
	hash           [32]byte
}

// parseHTLCParams extracts HTLC parameters from fuzz data.
func parseHTLCParams(data []byte, offset int,
	attemptID uint64) (HTLCFuzzParams, int) {

	params := HTLCFuzzParams{
		attemptID:      attemptID,
		addInvoice:     uint64(data[offset+1])%2 > 0,
		isRemoteSender: uint64(data[offset+2])%2 > 0,
		amount: lnwire.NewMSatFromSatoshis(
			btcutil.Amount(data[offset+3]) *
				btcutil.SatoshiPerBitcent,
		),
	}

	// Extract preimage from fuzz data.
	copy(
		params.preimage[:],
		data[offset+preimageOffset:offset+preimageOffset+preimageSize],
	)
	params.hash = sha256.Sum256(params.preimage[:])

	return params, offset + totalHTLCAddBytes
}

// addInvoiceToRegistry adds an invoice to the appropriate registry.
func (network *fuzzNetwork) addInvoiceToRegistry(params HTLCFuzzParams) {
	network.t.Helper()

	invoice := invoices.Invoice{
		CreationDate: time.Now(),
		Terms: invoices.ContractTerm{
			FinalCltvDelta:  testInvoiceCltvExpiry,
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

// createAddHTLCFromParams creates an HTLC from fuzz parameters.
func (network *fuzzNetwork) createAddHTLCFromParams(
	params HTLCFuzzParams) *lnwire.UpdateAddHTLC {

	network.t.Helper()

	if params.addInvoice {
		network.addInvoiceToRegistry(params)
	}

	// Select hop sequence based on forwarding direction and sender.
	var links []*channelLink
	switch {
	case params.isRemoteSender:
		links = []*channelLink{network.remoteLink}
	default:
		links = []*channelLink{network.localLink}
	}

	htlcAmt, totalTimelock, hops := generateHops(
		params.amount, testStartingHeight, links...,
	)

	blob, err := generateRoute(hops...)
	require.NoError(network.t, err)

	return &lnwire.UpdateAddHTLC{
		PaymentHash: params.hash,
		Amount:      htlcAmt,
		Expiry:      totalTimelock,
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
	if offset+totalHTLCAddBytes > len(network.data) {
		return len(network.data)
	}

	// Send HTLC through the appropriate link.
	var (
		link         *channelLink
		targetChanID lnwire.ShortChannelID
	)

	params, newOffset := parseHTLCParams(network.data, offset, attemptID)
	if params.isRemoteSender {
		link = network.remoteLink
		targetChanID = network.remoteLink.ShortChanID()
	} else {
		link = network.localLink
		targetChanID = network.localLink.ShortChanID()

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
		outgoingChanID: targetChanID,
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

	return newOffset
}

// processCommitSig handles sending a CommitSig message to the peer.
func (network *fuzzNetwork) processCommitSig(offset int) int {
	network.t.Helper()

	// Ensure we have enough data for CommitSignatures.
	if offset+stateExchangeOffset > len(network.data) {
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
	// update messages on the sender side.
	pending := sender.channel.NumPendingUpdates(
		lntypes.Local, lntypes.Remote,
	)
	if pending > 0 {
		_ = sender.updateCommitTx(network.t.Context())
	}

	return offset + stateExchangeOffset
}

// processUpdateFee handles sending a UpdateFee message to the peer.
func (network *fuzzNetwork) processUpdateFee(offset int) int {
	network.t.Helper()

	// Ensure we have enough data for UpdateFee.
	if offset+updateFeeOffset > len(network.data) {
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
			btcutil.Amount(network.data[offset+2])*10000,
		))

	return offset + updateFeeOffset
}

// processStfu drives the quiescence (stfu) state transition for a channel link.
func (network *fuzzNetwork) processStfu(offset int) int {
	network.t.Helper()

	// Ensure we have enough data to drive the stfu transition.
	if offset+stfuStateOffset > len(network.data) {
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

	if (network.data[offset+2] % 2) == 0 {
		// Send the stfu message.
		req, _ := fn.NewReq[fn.Unit, fn.Result[lntypes.ChannelParty]](
			fn.Unit{},
		)
		_ = node.handleQuiescenceReq(req)
	} else {
		// Stop the quiescence state.
		node.quiescer.Resume()
	}

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
		if cursor+n > len(network.data) {
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
		if canMutate(2, true) {
			out.ID = uint64(network.data[cursor])
			cursor++
		}

		// Amount
		if canMutate(2, true) {
			out.Amount = lnwire.NewMSatFromSatoshis(
				btcutil.Amount(network.data[cursor]) *
					btcutil.SatoshiPerBitcent,
			)
			cursor++
		}

		// Expiry
		if canMutate(2, true) {
			out.Expiry = uint32(network.data[cursor])
			cursor++
		}

		// OnionBlob
		if canMutate(1367, true) {
			copy(out.OnionBlob[:], network.data[cursor:cursor+1366])
			cursor += 1366
		}

		return &out, cursor

	case *lnwire.UpdateFulfillHTLC:
		out := *m

		// ID
		if canMutate(2, true) {
			out.ID = uint64(network.data[cursor])
			cursor++
		}

		// PaymentPreimage
		if canMutate(33, true) {
			copy(
				out.PaymentPreimage[:],
				network.data[cursor:cursor+32],
			)
			cursor += 32
		}

		return &out, cursor

	case *lnwire.UpdateFailMalformedHTLC:
		out := *m

		// ID
		if canMutate(2, true) {
			out.ID = uint64(network.data[cursor])
			cursor++
		}

		// FailureCode
		if canMutate(2, true) {
			out.FailureCode = lnwire.FailCode(network.data[cursor])
			cursor++
		}

		// ShaOnionBlob
		if canMutate(33, true) {
			copy(
				out.ShaOnionBlob[:],
				network.data[cursor:cursor+32],
			)
			cursor += 32
		}

		return &out, cursor

	case *lnwire.UpdateFailHTLC:
		out := *m

		// ID
		if canMutate(2, true) {
			out.ID = uint64(network.data[cursor])
			cursor++
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
			}
		}

		return &out, cursor

	case *lnwire.CommitSig:
		out := *m

		// CommitSig
		if canMutate(33, true) {
			if sig, err := lnwire.NewSigFromWireECDSA(
				network.data[cursor : cursor+32],
			); err == nil {
				out.CommitSig = sig
			}
			cursor += 32
		}

		// HTLC sigs
		if canMutate(33, true) {
			if sig, err := lnwire.NewSigFromWireECDSA(
				network.data[cursor : cursor+32],
			); err == nil {
				out.HtlcSigs = []lnwire.Sig{sig}
			}
			cursor += 32
		}

		return &out, cursor

	case *lnwire.RevokeAndAck:
		out := *m

		// Revocation
		if canMutate(33, true) {
			copy(out.Revocation[:], network.data[cursor:cursor+32])
			cursor += 32
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
	if offset+reorderMsgOffset > len(network.data) {
		return len(network.data)
	}

	// skip reordering for even selector bytes.
	if network.data[offset]%2 == 0 {
		return offset + 1
	}

	// Reordering is applied only to messages sent by the remote peer.
	peer, ok := network.remoteLink.cfg.Peer.(*mockPeer)
	require.True(network.t, ok)
	sentMsgs := peer.sentMsgs

reorder:
	for i := 0; i < int(network.data[offset+1]); i++ {
		select {
		case msg := <-sentMsgs:
			// Re-inject the message to reorder delivery.
			_ = network.remoteLink.cfg.Peer.SendMessage(false, msg)
		default:
			// No more messages available to reorder.
			break reorder
		}
	}

	return offset + reorderMsgOffset
}

// exchangeUpdates handles message sending between peers.
func (network *fuzzNetwork) exchangeUpdates(offset int) int {
	network.t.Helper()

	// Ensure we have enough data for exchanging updates.
	if offset+stateExchangeOffset > len(network.data) {
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
		mayBeMalformedMsg, cursor := network.maybeMalformMessage(msg,
			offset, isRemoteSender,
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

// runHTLCFuzzStateMachine executes the HTLC state machine with fuzz input data.
func (network *fuzzNetwork) runHTLCFuzzStateMachine() {
	network.t.Helper()

	htlcID := uint64(0)

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
		}
	}
}

// FuzzHTLCStates fuzz-tests the HTLC state machine. It gets the input data and
// performs operations such as add, revoke, commit, fulfill, or fail  etc.
// Message exchange is controlled using mock peer instances so we can precisely
// manage transport-layer messaging and uncover edge cases. The primary goal is
// to ensure that after all HTLC operations, channels never become out of sync
// or force close unexpectedly.
func FuzzHTLCStates(f *testing.F) {
	// Adding appropriate htlc state machine seed inputs.
	preimageR := make([]byte, 0, preimageSize)
	preimageL := make([]byte, 0, preimageSize)
	for i := range preimageSize {
		preimageR = append(preimageR, byte(i))
		preimageL = append(preimageL, byte(preimageSize-i-1))
	}
	// Remote -> Local : Fulfill
	remoteFulfill := append(
		[]byte{byte(sendAddHTLC), 1, 1, 1},
		append(
			preimageR,
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
		)...,
	)
	// Local -> Remote : Fail
	localFail := append(
		[]byte{byte(sendAddHTLC), 0, 0, 1},
		append(
			preimageL,
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
		)...,
	)
	f.Add(append(remoteFulfill, localFail...))

	f.Fuzz(func(t *testing.T, data []byte) {
		network := setupFuzzNetwork(t, data)

		// Execute the HTLC state machine with fuzz input.
		network.runHTLCFuzzStateMachine()
	})
}
