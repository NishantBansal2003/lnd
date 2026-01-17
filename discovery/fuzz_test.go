package discovery

import (
	"sync/atomic"
	"testing"
	"time"

	"github.com/btcsuite/btcd/btcec/v2"
	"github.com/btcsuite/btcd/chaincfg/chainhash"
	"github.com/lightningnetwork/lnd/lnwire"
	tmock "github.com/stretchr/testify/mock"
	"github.com/stretchr/testify/require"
)

const (
	// Channel and timeout constants
	sentMessageBufferSize = 100

	// Data offset requirements for actions
	minOffsetForAction = 1
	minOffsetWithPeer  = 2
	minOffsetWithData  = 3
	midOffsetWithData  = 4
	maxOffsetWithData  = 5

	// Maximum number of fuzz actions
	maxFuzzActions = 15
)

// FuzzAction represents the type of action to perform during fuzz testing. Each
// action corresponds to a different gossip protocol operation.
type FuzzAction uint8

const (
	// Local broadcast Node announcement
	FuzzActionLocalNodeAnn FuzzAction = iota

	// Local broadcast Channel Announcement
	FuzzActionLocalChannelAnn

	// Local broadcast Channel Update
	FuzzActionLocalChannelUpdate

	// Remote broadcast Node announcement
	FuzzActionRemoteNodeAnn

	// Remote broadcast Channel Announcement
	FuzzActionRemoteChannelAnn

	// Remote broadcast Channel Update
	FuzzActionRemoteChannelUpdate

	// Local Send the AnnouncementSignatures
	FuzzActionLocalAnnSignatures

	// Remote Send the AnnouncementSignatures
	FuzzActionRemoteAnnSignatures

	// New Peer connected to us
	FuzzActionConnectPeer

	// Peer disconnected from us
	FuzzActionDisconnectPeer

	// Remote Send the QueryShortChanIDs
	FuzzActionRemoteQueryShortChanIDs

	// Remote Send the QueryChannelRange
	FuzzActionRemoteQueryChannelRange

	// Remote Send the ReplyChannelRange
	FuzzActionRemoteReplyChannelRange

	// Remote Send the GossipTimestampRange
	FuzzActionRemoteGossipTimestampRange

	// Remote Send the ReplyShortChanIDsEnd
	FuzzActionRemoteReplyShortChanIDsEnd
)

// String returns a human-readable description of the fuzz action.
func (fa FuzzAction) String() string {
	switch fa {
	case FuzzActionLocalNodeAnn:
		return "LocalNodeAnnouncement"
	case FuzzActionLocalChannelAnn:
		return "LocalChannelAnnouncement"
	case FuzzActionLocalChannelUpdate:
		return "LocalChannelUpdate"
	case FuzzActionLocalAnnSignatures:
		return "LocalAnnouncementSignatures"
	case FuzzActionRemoteNodeAnn:
		return "RemoteNodeAnnouncement"
	case FuzzActionRemoteChannelAnn:
		return "RemoteChannelAnnouncement"
	case FuzzActionRemoteChannelUpdate:
		return "RemoteChannelUpdate"
	case FuzzActionRemoteAnnSignatures:
		return "RemoteAnnouncementSignatures"
	case FuzzActionRemoteQueryShortChanIDs:
		return "RemoteQueryShortChanIDs"
	case FuzzActionRemoteQueryChannelRange:
		return "RemoteQueryChannelRange"
	case FuzzActionRemoteReplyChannelRange:
		return "RemoteReplyChannelRange"
	case FuzzActionRemoteGossipTimestampRange:
		return "RemoteGossipTimestampRange"
	case FuzzActionRemoteReplyShortChanIDsEnd:
		return "RemoteReplyShortChanIDsEnd"
	case FuzzActionConnectPeer:
		return "ConnectPeer"
	case FuzzActionDisconnectPeer:
		return "DisconnectPeer"
	default:
		return "UnknownAction"
	}
}

// NewFuzzActionFromByte creates a FuzzAction from a raw byte value. It ensures
// the resulting action is always valid.
func NewFuzzActionFromByte(b byte) FuzzAction {
	return FuzzAction(b % uint8(maxFuzzActions))
}

// gossipPeer represents a mock peer connection with its associated private key.
type gossipPeer struct {
	connection *mockPeer
	privateKey *btcec.PrivateKey
}

// fuzzNetwork encapsulates the complete fuzz testing environment for the gossip
// system. It manages the underlying gossip test context and collection of
// connected peers.
type fuzzNetwork struct {
	ctx   *testCtx
	peers []*gossipPeer
}

// newFuzzNetwork initializes a new fuzz testing environment for gossip network
// testing.
func newFuzzNetwork(t *testing.T) *fuzzNetwork {
	t.Helper()

	// Start with a reasonable block height to avoid premature announcements
	testCtx, err := createTestCtx(t, 500, false)
	require.NoError(t, err)

	// Set up unlimited blockchain mocks for async validation.
	info := makeFundingTxInBlock(testCtx.t)
	testCtx.chain.On("GetBlockHash", tmock.Anything).Return(
		&chainhash.Hash{}, nil,
	).Maybe()
	testCtx.chain.On("GetBlock", tmock.Anything).Return(
		info.fundingBlock, nil,
	).Maybe()
	testCtx.chain.On(
		"GetUtxo", tmock.Anything, tmock.Anything, tmock.Anything,
		tmock.Anything,
	).Return(info.fundingTx, nil).Maybe()

	return &fuzzNetwork{
		ctx:   testCtx,
		peers: make([]*gossipPeer, 0),
	}
}

// connectNewPeer creates a new peer connection and adds it to the network.
func (fn *fuzzNetwork) connectNewPeer() {
	fn.ctx.t.Helper()

	privateKey, err := btcec.NewPrivateKey()
	require.NoError(fn.ctx.t, err)

	sentMsgs := make(chan lnwire.Message, sentMessageBufferSize)
	peer := &mockPeer{
		pk:           privateKey.PubKey(),
		sentMsgs:     sentMsgs,
		quit:         fn.ctx.gossiper.quit,
		disconnected: atomic.Bool{},
	}

	fn.ctx.gossiper.InitSyncState(peer)
	fn.peers = append(fn.peers, &gossipPeer{
		connection: peer,
		privateKey: privateKey,
	})
}

// hasPeers returns true if the network has any connected peers.
func (fn *fuzzNetwork) hasPeers() bool {
	return len(fn.peers) > 0
}

// validateDataOffset checks if there's enough data available at the specified
// offset.
func validateDataOffset(data []byte, offset, required int) bool {
	return len(data) > offset+required
}

// disconnectPeer removes a peer from the network based on fuzz data.
func (fn *fuzzNetwork) disconnectPeer(data []byte, offset int) int {
	fn.ctx.t.Helper()

	if !fn.hasPeers() {
		return offset + minOffsetForAction
	}

	if !validateDataOffset(data, offset, minOffsetForAction) {
		return len(data)
	}

	peerIndex := int(data[offset+1]) % len(fn.peers)
	peerToDisconnect := fn.peers[peerIndex]

	fn.ctx.gossiper.PruneSyncState(peerToDisconnect.connection.PubKey())
	fn.peers = append(fn.peers[:peerIndex], fn.peers[peerIndex+1:]...)

	return offset + minOffsetWithPeer
}

// selectPeer returns a peer from the network based on the selector byte.
// Returns nil if the peer list is empty.
func (fn *fuzzNetwork) selectPeer(selector byte) *gossipPeer {
	fn.ctx.t.Helper()

	if !fn.hasPeers() {
		return nil
	}
	peerIndex := int(selector) % len(fn.peers)
	return fn.peers[peerIndex]
}

// selectTimestamp returns either current timestamp or data-based timestamp
// based on the selector bit.
func selectTimestamp(dataTimestamp uint32) uint32 {
	currentTime := uint32(time.Now().Unix())

	if dataTimestamp%2 == 1 {
		return currentTime
	}

	return currentTime - dataTimestamp
}

// sendLocalNodeAnnouncement creates and processes a local node announcement.
// Returns the next offset to process in the data slice.
func (fn *fuzzNetwork) sendLocalNodeAnnouncement(localPrivKey *btcec.PrivateKey,
	data []byte, offset int) int {

	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, minOffsetForAction) {
		return len(data)
	}

	timestamp := selectTimestamp(uint32(data[offset+1]))
	nodeAnn, err := createNodeAnnouncement(
		localPrivKey, timestamp,
	)
	require.NoError(fn.ctx.t, err)

	fn.ctx.gossiper.ProcessLocalAnnouncement(nodeAnn)

	return offset + minOffsetWithPeer
}

// sendLocalChannelAnnouncement creates and processes a local channel
// announcement. Returns the next offset to process in the data slice.
func (fn *fuzzNetwork) sendLocalChannelAnnouncement(
	localPrivKey *btcec.PrivateKey, data []byte, offset int) int {

	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, minOffsetWithPeer) {
		return len(data)
	}

	peer := fn.selectPeer(data[offset+1])
	if peer == nil {
		return offset + minOffsetForAction
	}

	channelAnn, err := fn.ctx.createChannelAnnouncement(
		uint32(data[offset+2]), localPrivKey, peer.privateKey,
		withFundingTxPrep(fundingTxPrepTypeNone),
	)
	require.NoError(fn.ctx.t, err)

	fn.ctx.gossiper.ProcessLocalAnnouncement(channelAnn)

	return offset + minOffsetWithData
}

// sendLocalChannelUpdate creates and processes a local channel update. Returns
// the next offset to process in the data slice.
func (fn *fuzzNetwork) sendLocalChannelUpdate(localPrivKey *btcec.PrivateKey,
	data []byte, offset int) int {

	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, midOffsetWithData) {
		return len(data)
	}

	peer := fn.selectPeer(data[offset+1])
	if peer == nil {
		return offset + minOffsetForAction
	}

	updateAnn, err := createUpdateAnnouncement(
		uint32(data[offset+2]),
		lnwire.ChanUpdateChanFlags(data[offset+3]%2), localPrivKey,
		uint32(data[offset+4]),
	)
	require.NoError(fn.ctx.t, err)

	fn.ctx.gossiper.ProcessLocalAnnouncement(updateAnn)

	return offset + maxOffsetWithData
}

// sendRemoteNodeAnnouncement creates and processes a remote node announcement.
// Returns the next offset to process in the data slice.
func (fn *fuzzNetwork) sendRemoteNodeAnnouncement(data []byte, offset int) int {
	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, minOffsetWithPeer) {
		return len(data)
	}

	peer := fn.selectPeer(data[offset+1])
	if peer == nil {
		return offset + minOffsetForAction
	}

	timestamp := selectTimestamp(uint32(data[offset+1]))
	nodeAnn, err := createNodeAnnouncement(
		peer.privateKey, timestamp,
	)
	require.NoError(fn.ctx.t, err)

	fn.ctx.gossiper.ProcessRemoteAnnouncement(
		fn.ctx.t.Context(), nodeAnn, peer.connection,
	)

	return offset + minOffsetWithData
}

// sendRemoteChannelAnnouncement creates and processes a remote channel
// announcement. Returns the next offset to process in the data slice.
func (fn *fuzzNetwork) sendRemoteChannelAnnouncement(
	localPrivKey *btcec.PrivateKey, data []byte, offset int) int {

	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, minOffsetWithPeer) {
		return len(data)
	}

	peer := fn.selectPeer(data[offset+1])
	if peer == nil {
		return offset + minOffsetForAction
	}

	channelAnn, err := fn.ctx.createChannelAnnouncement(
		uint32(data[offset+2]), peer.privateKey, localPrivKey,
		withFundingTxPrep(fundingTxPrepTypeNone),
	)
	require.NoError(fn.ctx.t, err)

	fn.ctx.gossiper.ProcessRemoteAnnouncement(
		fn.ctx.t.Context(), channelAnn, peer.connection,
	)

	return offset + minOffsetWithData
}

// sendRemoteChannelUpdate creates and processes a remote channel update.
// Returns the next offset to process in the data slice.
func (fn *fuzzNetwork) sendRemoteChannelUpdate(data []byte, offset int) int {
	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, midOffsetWithData) {
		return len(data)
	}

	peer := fn.selectPeer(data[offset+1])
	if peer == nil {
		return offset + minOffsetForAction
	}

	updateAnn, err := createUpdateAnnouncement(
		uint32(data[offset+2]),
		lnwire.ChanUpdateChanFlags(data[offset+3]%2),
		peer.privateKey,
		uint32(data[offset+4]),
	)
	require.NoError(fn.ctx.t, err)

	fn.ctx.gossiper.ProcessRemoteAnnouncement(
		fn.ctx.t.Context(), updateAnn, peer.connection,
	)

	return offset + maxOffsetWithData
}

// sendLocalAnnounceSignatures creates and processes a local announcement
// signature. Returns the next offset to process in the data slice.
func (fn *fuzzNetwork) sendLocalAnnounceSignatures(
	localPrivKey *btcec.PrivateKey, data []byte, offset int) int {

	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, minOffsetWithPeer) {
		return len(data)
	}

	peer := fn.selectPeer(data[offset+1])
	if peer == nil {
		return offset + minOffsetForAction
	}

	chanAnn, err := fn.ctx.createChannelAnnouncement(
		uint32(data[offset+2]), localPrivKey, peer.privateKey,
		withFundingTxPrep(fundingTxPrepTypeNone),
	)
	require.NoError(fn.ctx.t, err)

	localAnnSign := &lnwire.AnnounceSignatures1{
		ShortChannelID: lnwire.ShortChannelID{
			BlockHeight: uint32(data[offset+2]),
		},
		NodeSignature:    chanAnn.NodeSig1,
		BitcoinSignature: chanAnn.BitcoinSig1,
	}
	fn.ctx.gossiper.ProcessLocalAnnouncement(localAnnSign)

	return offset + minOffsetWithData
}

// sendRemoteAnnounceSignatures creates and processes a remote announcement
// signature. Returns the next offset to process in the data slice.
func (fn *fuzzNetwork) sendRemoteAnnounceSignatures(
	localPrivKey *btcec.PrivateKey, data []byte, offset int) int {

	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, minOffsetWithPeer) {
		return len(data)
	}

	peer := fn.selectPeer(data[offset+1])
	if peer == nil {
		return offset + minOffsetForAction
	}

	chanAnn, err := fn.ctx.createChannelAnnouncement(
		uint32(data[offset+2]), localPrivKey, peer.privateKey,
		withFundingTxPrep(fundingTxPrepTypeNone),
	)
	require.NoError(fn.ctx.t, err)

	remoteAnn := &lnwire.AnnounceSignatures1{
		ShortChannelID: lnwire.ShortChannelID{
			BlockHeight: uint32(data[offset+2]),
		},
		NodeSignature:    chanAnn.NodeSig2,
		BitcoinSignature: chanAnn.BitcoinSig2,
	}
	fn.ctx.gossiper.ProcessRemoteAnnouncement(
		fn.ctx.t.Context(), remoteAnn, peer.connection,
	)

	return offset + minOffsetWithData
}

// sendRemoteQueryShortChanIDs creates and processes a remote query short
// channel IDs request. Returns the next offset to process in the data slice.
func (fn *fuzzNetwork) sendRemoteQueryShortChanIDs(data []byte,
	offset int) int {

	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, minOffsetWithPeer) {
		return len(data)
	}

	peer := fn.selectPeer(data[offset+1])
	if peer == nil {
		return offset + minOffsetForAction
	}

	queryShortChanIDs := &lnwire.QueryShortChanIDs{
		ChainHash: fn.ctx.gossiper.syncMgr.cfg.ChainHash,
		ShortChanIDs: []lnwire.ShortChannelID{
			{
				BlockHeight: uint32(data[offset+2]),
				TxIndex:     0,
				TxPosition:  0,
			},
		},
	}
	fn.ctx.gossiper.ProcessRemoteAnnouncement(
		fn.ctx.t.Context(), queryShortChanIDs, peer.connection,
	)

	return offset + minOffsetWithData
}

// sendRemoteQueryChannelRange creates and processes a remote query channel
// range request. Returns the next offset to process in the data slice.
func (fn *fuzzNetwork) sendRemoteQueryChannelRange(data []byte,
	offset int) int {

	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, minOffsetWithData) {
		return len(data)
	}

	peer := fn.selectPeer(data[offset+1])
	if peer == nil {
		return offset + minOffsetForAction
	}

	queryChannelRange := &lnwire.QueryChannelRange{
		ChainHash:        fn.ctx.gossiper.syncMgr.cfg.ChainHash,
		FirstBlockHeight: uint32(data[offset+2]),
		NumBlocks:        uint32(data[offset+3]),
	}
	fn.ctx.gossiper.ProcessRemoteAnnouncement(
		fn.ctx.t.Context(), queryChannelRange, peer.connection,
	)

	return offset + midOffsetWithData
}

// sendRemoteReplyChannelRange creates and processes a remote reply channel
// range response. Returns the next offset to process in the data slice.
func (fn *fuzzNetwork) sendRemoteReplyChannelRange(data []byte,
	offset int) int {

	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, midOffsetWithData) {
		return len(data)
	}

	peer := fn.selectPeer(data[offset+1])
	if peer == nil {
		return offset + minOffsetForAction
	}

	replyChannelRange := &lnwire.ReplyChannelRange{
		ChainHash:        fn.ctx.gossiper.syncMgr.cfg.ChainHash,
		FirstBlockHeight: uint32(data[offset+2]),
		NumBlocks:        uint32(data[offset+3]),
		ShortChanIDs: []lnwire.ShortChannelID{
			{
				BlockHeight: uint32(data[offset+4]),
				TxIndex:     0,
				TxPosition:  0,
			},
		},
		Complete: 1,
	}
	fn.ctx.gossiper.ProcessRemoteAnnouncement(
		fn.ctx.t.Context(), replyChannelRange, peer.connection,
	)

	return offset + maxOffsetWithData
}

// sendRemoteReplyShortChanIDsEnd creates and processes a remote reply short
// channel IDs end. Returns the next offset to process in the data slice.
func (fn *fuzzNetwork) sendRemoteReplyShortChanIDsEnd(data []byte,
	offset int) int {

	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, minOffsetForAction) {
		return len(data)
	}

	peer := fn.selectPeer(data[offset+1])
	if peer == nil {
		return offset + minOffsetForAction
	}

	replyShortChanIDsEnd := &lnwire.ReplyShortChanIDsEnd{
		ChainHash: fn.ctx.gossiper.syncMgr.cfg.ChainHash,
		Complete:  1,
	}
	fn.ctx.gossiper.ProcessRemoteAnnouncement(
		fn.ctx.t.Context(), replyShortChanIDsEnd, peer.connection,
	)

	return offset + minOffsetWithPeer
}

// sendRemoteGossipTimestampRange creates and processes a remote gossip
// timestamp range. Returns the next offset to process in the data slice.
func (fn *fuzzNetwork) sendRemoteGossipTimestampRange(data []byte,
	offset int) int {

	fn.ctx.t.Helper()

	if !validateDataOffset(data, offset, minOffsetWithData) {
		return len(data)
	}

	peer := fn.selectPeer(data[offset+1])
	if peer == nil {
		return offset + minOffsetForAction
	}

	gossipTimestampRange := &lnwire.GossipTimestampRange{
		ChainHash:      fn.ctx.gossiper.syncMgr.cfg.ChainHash,
		FirstTimestamp: uint32(data[offset+2]),
		TimestampRange: uint32(data[offset+3]),
	}
	fn.ctx.gossiper.ProcessRemoteAnnouncement(
		fn.ctx.t.Context(), gossipTimestampRange, peer.connection,
	)

	return offset + midOffsetWithData
}

// runGossipStateMachine executes a fuzz test scenario by interpreting the
// provided data bytes as a sequence of actions to perform on the gossip
// network. Each byte determines what type of gossip operation should be
// executed (node announcements, channel announcements, peer connections, etc.).
func (fn *fuzzNetwork) runGossipStateMachine(data []byte) {
	fn.ctx.t.Helper()

	localPrivateKey, err := btcec.NewPrivateKey()
	require.NoError(fn.ctx.t, err)

	for offset := 0; offset < len(data); {
		action := NewFuzzActionFromByte(data[offset])

		switch action {
		case FuzzActionLocalNodeAnn:
			// Local broadcast Node announcement
			offset = fn.sendLocalNodeAnnouncement(
				localPrivateKey, data, offset,
			)

		case FuzzActionLocalChannelAnn:
			// Local broadcast Channel Announcement
			offset = fn.sendLocalChannelAnnouncement(
				localPrivateKey, data, offset,
			)

		case FuzzActionLocalChannelUpdate:
			// Local broadcast Channel Update
			offset = fn.sendLocalChannelUpdate(
				localPrivateKey, data, offset,
			)

		case FuzzActionRemoteNodeAnn:
			// Peer broadcast Node announcement
			offset = fn.sendRemoteNodeAnnouncement(data, offset)

		case FuzzActionRemoteChannelAnn:
			// Peer broadcast Channel Announcement
			offset = fn.sendRemoteChannelAnnouncement(
				localPrivateKey, data, offset,
			)

		case FuzzActionRemoteChannelUpdate:
			// Peer broadcast Channel Update
			offset = fn.sendRemoteChannelUpdate(data, offset)

		case FuzzActionLocalAnnSignatures:
			// Local Send the AnnouncementSignatures
			offset = fn.sendLocalAnnounceSignatures(
				localPrivateKey, data, offset,
			)

		case FuzzActionRemoteAnnSignatures:
			// Remote Send the AnnouncementSignatures
			offset = fn.sendRemoteAnnounceSignatures(
				localPrivateKey, data, offset,
			)

		case FuzzActionConnectPeer:
			// New Peer connected to us
			fn.connectNewPeer()
			offset++

		case FuzzActionDisconnectPeer:
			// Peer disconnected from us
			offset = fn.disconnectPeer(data, offset)

		case FuzzActionRemoteQueryShortChanIDs:
			// Remote Send the QueryShortChanIDs
			offset = fn.sendRemoteQueryShortChanIDs(data, offset)

		case FuzzActionRemoteQueryChannelRange:
			// Remote Send the QueryChannelRange
			offset = fn.sendRemoteQueryChannelRange(data, offset)

		case FuzzActionRemoteReplyChannelRange:
			// Remote Send the ReplyChannelRange
			offset = fn.sendRemoteReplyChannelRange(data, offset)

		case FuzzActionRemoteGossipTimestampRange:
			// Remote Send the GossipTimestampRange
			offset = fn.sendRemoteGossipTimestampRange(data, offset)

		case FuzzActionRemoteReplyShortChanIDsEnd:
			// Remote Send the ReplyShortChanIDsEnd
			offset = fn.sendRemoteReplyShortChanIDsEnd(data, offset)
		}

		select {
		case <-fn.ctx.broadcastedMessage:
		default:
		}
	}
}

// FuzzGossipMessages is the main fuzz testing entry point for the gossip
// system. It tests various combinations of gossip protocol messages and peer
// interactions to discover potential runtime issues and panics.
func FuzzGossipMessages(f *testing.F) {
	// Seed with a comprehensive sequence following gossip protocol order
	f.Add([]byte{
		// 1. Connect peers first
		uint8(FuzzActionConnectPeer),

		// 2. Node announcements (establish node identities)
		uint8(FuzzActionLocalNodeAnn), 1,
		uint8(FuzzActionRemoteNodeAnn), 0, 1,

		// 3. Channel announcements (establish channels)
		uint8(FuzzActionLocalChannelAnn), 0, 100,
		uint8(FuzzActionRemoteChannelAnn), 1, 101,

		// 4. Channel updates (set channel policies)
		uint8(FuzzActionLocalChannelUpdate), 0, 102, 0, 1,
		uint8(FuzzActionRemoteChannelUpdate), 1, 103, 1, 2,

		// 5. Announcement signatures (complete channel announcement flow)
		uint8(FuzzActionLocalAnnSignatures), 0, 104,
		uint8(FuzzActionRemoteAnnSignatures), 1, 105,

		// 6. Query operations (sync protocol)
		uint8(FuzzActionRemoteQueryChannelRange), 0, 1, 10,
		uint8(FuzzActionRemoteReplyChannelRange), 1, 1, 10, 106,
		uint8(FuzzActionRemoteQueryShortChanIDs), 0, 107,
		uint8(FuzzActionRemoteReplyShortChanIDsEnd), 1,

		// 7. Gossip timestamp range (time-based sync)
		uint8(FuzzActionRemoteGossipTimestampRange), 0, 1, 100,

		// 8. Disconnect one peer at the end
		uint8(FuzzActionDisconnectPeer), 0,
	})

	f.Fuzz(func(t *testing.T, data []byte) {
		network := newFuzzNetwork(t)
		network.runGossipStateMachine(data)
	})
}
