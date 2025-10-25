// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Copyright (c) 2022 The Luckycoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "validation.h"

#include "arith_uint256.h"
#include "chainparams.h"
#include "checkpoints.h"
#include "checkqueue.h"
#include "consensus/consensus.h"
#include "consensus/merkle.h"
#include "consensus/validation.h"
#include "luckycoin.h"
#include "luckycoin-fees.h"
#include "hash.h"
#include "init.h"
#include "policy/fees.h"
#include "policy/policy.h"
#include "pow.h"
#include "primitives/block.h"
#include "primitives/pureheader.h"
#include "primitives/transaction.h"
#include "random.h"
#include "script/script.h"
#include "script/sigcache.h"
#include "script/standard.h"
#include "timedata.h"
#include "tinyformat.h"
#include "txdb.h"
#include "txmempool.h"
#include "ui_interface.h"
#include "undo.h"
#include "util.h"
#include "utilmoneystr.h"
#include "utilstrencodings.h"
#include "validationinterface.h"
#include "versionbits.h"
#include "warnings.h"
#include "base58.h"

#include <atomic>
#include <sstream>

#include <boost/algorithm/string/replace.hpp>
#include <boost/algorithm/string/join.hpp>
#include <boost/bind/bind.hpp>
#include <boost/filesystem.hpp>
#include <boost/filesystem/fstream.hpp>
#include <boost/math/distributions/poisson.hpp>
#include <boost/thread.hpp>

#if defined(NDEBUG)
# error "Luckycoin cannot be compiled without assertions."
#endif

/**
 * Global state
 */

CCriticalSection cs_main;

BlockMap mapBlockIndex;
CChain chainActive;
CBlockIndex *pindexBestHeader = NULL;
CWaitableCriticalSection csBestBlock;
CConditionVariable cvBlockChange;
int nScriptCheckThreads = 0;
std::atomic_bool fImporting(false);
bool fReindex = false;
bool fTxIndex = false;
bool fHavePruned = false;
bool fPruneMode = false;
bool fIsBareMultisigStd = DEFAULT_PERMIT_BAREMULTISIG;
bool fRequireStandard = true;
bool fCheckBlockIndex = false;
bool fCheckpointsEnabled = DEFAULT_CHECKPOINTS_ENABLED;
size_t nCoinCacheUsage = 5000 * 300;
uint64_t nPruneTarget = 0;
int64_t nMaxTipAge = DEFAULT_MAX_TIP_AGE;
bool fEnableReplacement = DEFAULT_ENABLE_REPLACEMENT;

uint256 hashAssumeValid;

//mlumin 5/2021: Changing this variable to a fee rate, because that's what it is, not a fee. Confusion bad.
CFeeRate minRelayTxFeeRate = CFeeRate(DEFAULT_MIN_RELAY_TX_FEE);
CAmount maxTxFee = DEFAULT_TRANSACTION_MAXFEE;

CTxMemPool mempool(::minRelayTxFeeRate);

bool isBlacklisted(const uint160& scriptHash, const CChainParams& chainParams, int currentBlockHeight);

/**
 * Returns true if there are nRequired or more blocks of minVersion or above
 * in the last Consensus::Params::nMajorityWindow blocks, starting at pstart and going backwards.
 */
static bool IsSuperMajority(int minVersion, const CBlockIndex* pstart, unsigned nRequired, const Consensus::Params& consensusParams);
static void CheckBlockIndex(const Consensus::Params& consensusParams);

/** Constant stuff for coinbase transactions we create: */
CScript COINBASE_FLAGS;

const std::string strMessageMagic = "Luckycoin Signed Message:\n";

// Internal stuff
namespace {

    struct CBlockIndexWorkComparator
    {
        bool operator()(CBlockIndex *pa, CBlockIndex *pb) const {
            // First sort by most total work, ...
            if (pa->nChainWork > pb->nChainWork) return false;
            if (pa->nChainWork < pb->nChainWork) return true;

            // ... then by earliest time received, ...
            if (pa->nSequenceId < pb->nSequenceId) return false;
            if (pa->nSequenceId > pb->nSequenceId) return true;

            // Use pointer address as tie breaker (should only happen with blocks
            // loaded from disk, as those all have id 0).
            if (pa < pb) return false;
            if (pa > pb) return true;

            // Identical blocks.
            return false;
        }
    };

    CBlockIndex *pindexBestInvalid;

    /**
     * The set of all CBlockIndex entries with BLOCK_VALID_TRANSACTIONS (for itself and all ancestors) and
     * as good as our current tip or better. Entries may be failed, though, and pruning nodes may be
     * missing the data for the block.
     */
    std::set<CBlockIndex*, CBlockIndexWorkComparator> setBlockIndexCandidates;
    /** All pairs A->B, where A (or one of its ancestors) misses transactions, but B has transactions.
     * Pruned nodes may have entries where B is missing data.
     */
    std::multimap<CBlockIndex*, CBlockIndex*> mapBlocksUnlinked;

    CCriticalSection cs_LastBlockFile;
    std::vector<CBlockFileInfo> vinfoBlockFile;
    int nLastBlockFile = 0;
    /** Global flag to indicate we should check to see if there are
     *  block/undo files that should be deleted.  Set on startup
     *  or if we allocate more file space when we're in prune mode
     */
    bool fCheckForPruning = false;

    /**
     * Every received block is assigned a unique and increasing identifier, so we
     * know which one to give priority in case of a fork.
     */
    CCriticalSection cs_nBlockSequenceId;
    /** Blocks loaded from disk are assigned id 0, so start the counter at 1. */
    int32_t nBlockSequenceId = 1;
    /** Decreasing counter (used by subsequent preciousblock calls). */
    int32_t nBlockReverseSequenceId = -1;
    /** chainwork for the last block that preciousblock has been applied to. */
    arith_uint256 nLastPreciousChainwork = 0;

    /** In order to efficiently track invalidity of headers, we keep the set of
      * blocks which we tried to connect and found to be invalid here (ie which
      * were set to BLOCK_FAILED_VALID since the last restart). We can then
      * walk this set and check if a new header is a descendant of something in
      * this set, preventing us from having to walk mapBlockIndex when we try
      * to connect a bad block and fail.
      *
      * While this is more complicated than marking everything which descends
      * from an invalid block as invalid at the time we discover it to be
      * invalid, doing so would require walking all of mapBlockIndex to find all
      * descendants. Since this case should be very rare, keeping track of all
      * BLOCK_FAILED_VALID blocks in a set should be just fine and work just as
      * well.
      *
      * Because we already walk mapBlockIndex in height-order at startup, we go
      * ahead and mark descendants of invalid blocks as FAILED_CHILD at that time,
      * instead of putting things in this set.
      */
    std::set<CBlockIndex*> gFailedBlocks;

    /** Dirty block index entries. */
    std::set<CBlockIndex*> setDirtyBlockIndex;

    /** Dirty block file entries. */
    std::set<int> setDirtyFileInfo;
} // anon namespace

/* Use this class to start tracking transactions that are removed from the
 * mempool and pass all those transactions through SyncTransaction when the
 * object goes out of scope. This is currently only used to call SyncTransaction
 * on conflicts removed from the mempool during block connection.  Applied in
 * ActivateBestChain around ActivateBestStep which in turn calls:
 * ConnectTip->removeForBlock->removeConflicts
 */
class MemPoolConflictRemovalTracker
{
private:
    std::vector<CTransactionRef> conflictedTxs;
    CTxMemPool &pool;

public:
    MemPoolConflictRemovalTracker(CTxMemPool &_pool) : pool(_pool) {
        pool.NotifyEntryRemoved.connect(boost::bind(&MemPoolConflictRemovalTracker::NotifyEntryRemoved,
                                                    this, boost::placeholders::_1,
                                                    boost::placeholders::_2));
    }

    void NotifyEntryRemoved(CTransactionRef txRemoved, MemPoolRemovalReason reason) {
        if (reason == MemPoolRemovalReason::CONFLICT) {
            conflictedTxs.push_back(txRemoved);
        }
    }

    ~MemPoolConflictRemovalTracker() {
        pool.NotifyEntryRemoved.disconnect(boost::bind(&MemPoolConflictRemovalTracker::NotifyEntryRemoved,
                                                       this, boost::placeholders::_1,
                                                       boost::placeholders::_2));
        for (const auto& tx : conflictedTxs) {
            GetMainSignals().SyncTransaction(*tx, NULL, CMainSignals::SYNC_TRANSACTION_NOT_IN_BLOCK);
        }
        conflictedTxs.clear();
    }
};

CBlockIndex* FindForkInGlobalIndex(const CChain& chain, const CBlockLocator& locator)
{
    // Find the first block the caller has in the main chain
    BOOST_FOREACH(const uint256& hash, locator.vHave) {
        BlockMap::iterator mi = mapBlockIndex.find(hash);
        if (mi != mapBlockIndex.end())
        {
            CBlockIndex* pindex = (*mi).second;
            if (chain.Contains(pindex))
                return pindex;
            if (pindex->GetAncestor(chain.Height()) == chain.Tip()) {
                return chain.Tip();
            }
        }
    }
    return chain.Genesis();
}

CCoinsViewCache *pcoinsTip = NULL;
CBlockTreeDB *pblocktree = NULL;

enum FlushStateMode {
    FLUSH_STATE_NONE,
    FLUSH_STATE_IF_NEEDED,
    FLUSH_STATE_PERIODIC,
    FLUSH_STATE_ALWAYS
};

// See definition for documentation
bool static FlushStateToDisk(CValidationState &state, FlushStateMode mode, int nManualPruneHeight=0);
void FindFilesToPruneManual(std::set<int>& setFilesToPrune, int nManualPruneHeight);

bool IsFinalTx(const CTransaction &tx, int nBlockHeight, int64_t nBlockTime)
{
    if (tx.nLockTime == 0)
        return true;
    if ((int64_t)tx.nLockTime < ((int64_t)tx.nLockTime < LOCKTIME_THRESHOLD ? (int64_t)nBlockHeight : nBlockTime))
        return true;
    for (const auto& txin : tx.vin) {
        if (!(txin.nSequence == CTxIn::SEQUENCE_FINAL))
            return false;
    }
    return true;
}

bool CheckFinalTx(const CTransaction &tx, int flags)
{
    AssertLockHeld(cs_main);

    // By convention a negative value for flags indicates that the
    // current network-enforced consensus rules should be used. In
    // a future soft-fork scenario that would mean checking which
    // rules would be enforced for the next block and setting the
    // appropriate flags. At the present time no soft-forks are
    // scheduled, so no flags are set.
    flags = std::max(flags, 0);

    // CheckFinalTx() uses chainActive.Height()+1 to evaluate
    // nLockTime because when IsFinalTx() is called within
    // CBlock::AcceptBlock(), the height of the block *being*
    // evaluated is what is used. Thus if we want to know if a
    // transaction can be part of the *next* block, we need to call
    // IsFinalTx() with one more than chainActive.Height().
    const int nBlockHeight = chainActive.Height() + 1;

    // BIP113 will require that time-locked transactions have nLockTime set to
    // less than the median time of the previous block they're contained in.
    // When the next block is created its previous block will be the current
    // chain tip, so we use that to calculate the median time passed to
    // IsFinalTx() if LOCKTIME_MEDIAN_TIME_PAST is set.
    const int64_t nBlockTime = (flags & LOCKTIME_MEDIAN_TIME_PAST)
                             ? chainActive.Tip()->GetMedianTimePast()
                             : GetAdjustedTime();

    return IsFinalTx(tx, nBlockHeight, nBlockTime);
}

/**
 * Calculates the block height and previous block's median time past at
 * which the transaction will be considered final in the context of BIP 68.
 * Also removes from the vector of input heights any entries which did not
 * correspond to sequence locked inputs as they do not affect the calculation.
 */
static std::pair<int, int64_t> CalculateSequenceLocks(const CTransaction &tx, int flags, std::vector<int>* prevHeights, const CBlockIndex& block)
{
    assert(prevHeights->size() == tx.vin.size());

    // Will be set to the equivalent height- and time-based nLockTime
    // values that would be necessary to satisfy all relative lock-
    // time constraints given our view of block chain history.
    // The semantics of nLockTime are the last invalid height/time, so
    // use -1 to have the effect of any height or time being valid.
    int nMinHeight = -1;
    int64_t nMinTime = -1;

    // tx.nVersion is signed integer so requires cast to unsigned otherwise
    // we would be doing a signed comparison and half the range of nVersion
    // wouldn't support BIP 68.
    bool fEnforceBIP68 = static_cast<uint32_t>(tx.nVersion) >= 2
                      && flags & LOCKTIME_VERIFY_SEQUENCE;

    // Do not enforce sequence numbers as a relative lock time
    // unless we have been instructed to
    if (!fEnforceBIP68) {
        return std::make_pair(nMinHeight, nMinTime);
    }

    for (size_t txinIndex = 0; txinIndex < tx.vin.size(); txinIndex++) {
        const CTxIn& txin = tx.vin[txinIndex];

        // Sequence numbers with the most significant bit set are not
        // treated as relative lock-times, nor are they given any
        // consensus-enforced meaning at this point.
        if (txin.nSequence & CTxIn::SEQUENCE_LOCKTIME_DISABLE_FLAG) {
            // The height of this input is not relevant for sequence locks
            (*prevHeights)[txinIndex] = 0;
            continue;
        }

        int nCoinHeight = (*prevHeights)[txinIndex];

        if (txin.nSequence & CTxIn::SEQUENCE_LOCKTIME_TYPE_FLAG) {
            int64_t nCoinTime = block.GetAncestor(std::max(nCoinHeight-1, 0))->GetMedianTimePast();
            // NOTE: Subtract 1 to maintain nLockTime semantics
            // BIP 68 relative lock times have the semantics of calculating
            // the first block or time at which the transaction would be
            // valid. When calculating the effective block time or height
            // for the entire transaction, we switch to using the
            // semantics of nLockTime which is the last invalid block
            // time or height.  Thus we subtract 1 from the calculated
            // time or height.

            // Time-based relative lock-times are measured from the
            // smallest allowed timestamp of the block containing the
            // txout being spent, which is the median time past of the
            // block prior.
            nMinTime = std::max(nMinTime, nCoinTime + (int64_t)((txin.nSequence & CTxIn::SEQUENCE_LOCKTIME_MASK) << CTxIn::SEQUENCE_LOCKTIME_GRANULARITY) - 1);
        } else {
            nMinHeight = std::max(nMinHeight, nCoinHeight + (int)(txin.nSequence & CTxIn::SEQUENCE_LOCKTIME_MASK) - 1);
        }
    }

    return std::make_pair(nMinHeight, nMinTime);
}

static bool EvaluateSequenceLocks(const CBlockIndex& block, std::pair<int, int64_t> lockPair)
{
    assert(block.pprev);
    int64_t nBlockTime = block.pprev->GetMedianTimePast();
    if (lockPair.first >= block.nHeight || lockPair.second >= nBlockTime)
        return false;

    return true;
}

bool SequenceLocks(const CTransaction &tx, int flags, std::vector<int>* prevHeights, const CBlockIndex& block)
{
    return EvaluateSequenceLocks(block, CalculateSequenceLocks(tx, flags, prevHeights, block));
}

bool TestLockPointValidity(const LockPoints* lp)
{
    AssertLockHeld(cs_main);
    assert(lp);
    // If there are relative lock times then the maxInputBlock will be set
    // If there are no relative lock times, the LockPoints don't depend on the chain
    if (lp->maxInputBlock) {
        // Check whether chainActive is an extension of the block at which the LockPoints
        // calculation was valid.  If not LockPoints are no longer valid
        if (!chainActive.Contains(lp->maxInputBlock)) {
            return false;
        }
    }

    // LockPoints still valid
    return true;
}

bool CheckSequenceLocks(const CTransaction &tx, int flags, LockPoints* lp, bool useExistingLockPoints)
{
    AssertLockHeld(cs_main);
    AssertLockHeld(mempool.cs);

    CBlockIndex* tip = chainActive.Tip();
    CBlockIndex index;
    index.pprev = tip;
    // CheckSequenceLocks() uses chainActive.Height()+1 to evaluate
    // height based locks because when SequenceLocks() is called within
    // ConnectBlock(), the height of the block *being*
    // evaluated is what is used.
    // Thus if we want to know if a transaction can be part of the
    // *next* block, we need to use one more than chainActive.Height()
    index.nHeight = tip->nHeight + 1;

    std::pair<int, int64_t> lockPair;
    if (useExistingLockPoints) {
        assert(lp);
        lockPair.first = lp->height;
        lockPair.second = lp->time;
    }
    else {
        // pcoinsTip contains the UTXO set for chainActive.Tip()
        CCoinsViewMemPool viewMemPool(pcoinsTip, mempool);
        std::vector<int> prevheights;
        prevheights.resize(tx.vin.size());
        for (size_t txinIndex = 0; txinIndex < tx.vin.size(); txinIndex++) {
            const CTxIn& txin = tx.vin[txinIndex];
            CCoins coins;
            if (!viewMemPool.GetCoins(txin.prevout.hash, coins)) {
                return error("%s: Missing input", __func__);
            }
            if (coins.nHeight == MEMPOOL_HEIGHT) {
                // Assume all mempool transaction confirm in the next block
                prevheights[txinIndex] = tip->nHeight + 1;
            } else {
                prevheights[txinIndex] = coins.nHeight;
            }
        }
        lockPair = CalculateSequenceLocks(tx, flags, &prevheights, index);
        if (lp) {
            lp->height = lockPair.first;
            lp->time = lockPair.second;
            // Also store the hash of the block with the highest height of
            // all the blocks which have sequence locked prevouts.
            // This hash needs to still be on the chain
            // for these LockPoint calculations to be valid
            // Note: It is impossible to correctly calculate a maxInputBlock
            // if any of the sequence locked inputs depend on unconfirmed txs,
            // except in the special case where the relative lock time/height
            // is 0, which is equivalent to no sequence lock. Since we assume
            // input height of tip+1 for mempool txs and test the resulting
            // lockPair from CalculateSequenceLocks against tip+1.  We know
            // EvaluateSequenceLocks will fail if there was a non-zero sequence
            // lock on a mempool input, so we can use the return value of
            // CheckSequenceLocks to indicate the LockPoints validity
            int maxInputHeight = 0;
            BOOST_FOREACH(int height, prevheights) {
                // Can ignore mempool inputs since we'll fail if they had non-zero locks
                if (height != tip->nHeight+1) {
                    maxInputHeight = std::max(maxInputHeight, height);
                }
            }
            lp->maxInputBlock = tip->GetAncestor(maxInputHeight);
        }
    }
    return EvaluateSequenceLocks(index, lockPair);
}


unsigned int GetLegacySigOpCount(const CTransaction& tx)
{
    unsigned int nSigOps = 0;
    for (const auto& txin : tx.vin)
    {
        nSigOps += txin.scriptSig.GetSigOpCount(false);
    }
    for (const auto& txout : tx.vout)
    {
        nSigOps += txout.scriptPubKey.GetSigOpCount(false);
    }
    return nSigOps;
}

unsigned int GetP2SHSigOpCount(const CTransaction& tx, const CCoinsViewCache& inputs)
{
    if (tx.IsCoinBase())
        return 0;

    unsigned int nSigOps = 0;
    for (unsigned int i = 0; i < tx.vin.size(); i++)
    {
        const CTxOut &prevout = inputs.GetOutputFor(tx.vin[i]);
        if (prevout.scriptPubKey.IsPayToScriptHash())
            nSigOps += prevout.scriptPubKey.GetSigOpCount(tx.vin[i].scriptSig);
    }
    return nSigOps;
}

int64_t GetTransactionSigOpCost(const CTransaction& tx, const CCoinsViewCache& inputs, int flags)
{
    int64_t nSigOps = GetLegacySigOpCount(tx) * WITNESS_SCALE_FACTOR;

    if (tx.IsCoinBase())
        return nSigOps;

    if (flags & SCRIPT_VERIFY_P2SH) {
        nSigOps += GetP2SHSigOpCount(tx, inputs) * WITNESS_SCALE_FACTOR;
    }

    for (unsigned int i = 0; i < tx.vin.size(); i++)
    {
        const CTxOut &prevout = inputs.GetOutputFor(tx.vin[i]);
        nSigOps += CountWitnessSigOps(tx.vin[i].scriptSig, prevout.scriptPubKey, &tx.vin[i].scriptWitness, flags);
    }
    return nSigOps;
}





bool CheckTransaction(const CTransaction& tx, CValidationState &state, bool fCheckDuplicateInputs)
{
    // Basic checks that don't depend on any context
    if (tx.vin.empty())
        return state.DoS(10, false, REJECT_INVALID, "bad-txns-vin-empty");
    if (tx.vout.empty())
        return state.DoS(10, false, REJECT_INVALID, "bad-txns-vout-empty");
    // Size limits (this doesn't take the witness into account, as that hasn't been checked for malleability)
    if (::GetSerializeSize(tx, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS) > MAX_BLOCK_BASE_SIZE)
        return state.DoS(100, false, REJECT_INVALID, "bad-txns-oversize");

    // Check for negative or overflow output values
    CAmount nValueOut = 0;
    for (const auto& txout : tx.vout)
    {
        if (txout.nValue < 0)
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-vout-negative");
        if (txout.nValue > MAX_MONEY)
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-vout-toolarge");
        nValueOut += txout.nValue;
        if (!MoneyRange(nValueOut))
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-txouttotal-toolarge");
    }

    // Check for duplicate inputs - note that this check is slow so we skip it in CheckBlock
    if (fCheckDuplicateInputs) {
        std::set<COutPoint> vInOutPoints;
        for (const auto& txin : tx.vin)
        {
            if (!vInOutPoints.insert(txin.prevout).second)
                return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-duplicate");
        }
    }

    if (tx.IsCoinBase())
    {
        if (tx.vin[0].scriptSig.size() < 2 || tx.vin[0].scriptSig.size() > 220)
            return state.DoS(100, false, REJECT_INVALID, "bad-cb-length");
    }
    else
    {
        for (const auto& txin : tx.vin)
            if (txin.prevout.IsNull())
                return state.DoS(10, false, REJECT_INVALID, "bad-txns-prevout-null");
    }

    return true;
}

void LimitMempoolSize(CTxMemPool& pool, size_t limit, unsigned long age) {
    int expired = pool.Expire(GetTime() - age);
    if (expired != 0)
        LogPrint("mempool", "Expired %i transactions from the memory pool\n", expired);

    std::vector<uint256> vNoSpendsRemaining;
    pool.TrimToSize(limit, &vNoSpendsRemaining);
    BOOST_FOREACH(const uint256& removed, vNoSpendsRemaining)
        pcoinsTip->Uncache(removed);
}

/** Convert CValidationState to a human-readable message for logging */
std::string FormatStateMessage(const CValidationState &state)
{
    return strprintf("%s%s (code %i)",
        state.GetRejectReason(),
        state.GetDebugMessage().empty() ? "" : ", "+state.GetDebugMessage(),
        state.GetRejectCode());
}

static bool IsCurrentForFeeEstimation()
{
    AssertLockHeld(cs_main);
    if (IsInitialBlockDownload())
        return false;
    if (chainActive.Tip()->GetBlockTime() < (GetTime() - MAX_FEE_ESTIMATION_TIP_AGE))
        return false;
    if (chainActive.Height() < pindexBestHeader->nHeight - 1)
        return false;
    return true;
}

bool AcceptToMemoryPoolWorker(CTxMemPool& pool, CValidationState& state, const CTransactionRef& ptx, bool fLimitFree,
                              bool* pfMissingInputs, int64_t nAcceptTime, std::list<CTransactionRef>* plTxnReplaced,
                              bool fOverrideMempoolLimit, const CAmount& nAbsurdFee, std::vector<uint256>& vHashTxnToUncache)
{
    const CTransaction& tx = *ptx;
    const uint256 hash = tx.GetHash();
    AssertLockHeld(cs_main);
    if (pfMissingInputs)
        *pfMissingInputs = false;

    if (!CheckTransaction(tx, state))
        return false; // state filled in by CheckTransaction

    // Coinbase is only valid in a block, not as a loose transaction
    if (tx.IsCoinBase())
        return state.DoS(100, false, REJECT_INVALID, "coinbase");

    // Reject transactions with witness before segregated witness activates (override with -prematurewitness)
    bool witnessEnabled = IsWitnessEnabled(chainActive.Tip(), Params().GetConsensus(chainActive.Height()));
    if (!GetBoolArg("-prematurewitness",false) && tx.HasWitness() && !witnessEnabled) {
        return state.DoS(0, false, REJECT_NONSTANDARD, "no-witness-yet", true);
    }

    ChainSigVersion chainSigVersion = GetChainSigVersion(chainActive.Tip(), Params().GetConsensus(chainActive.Height()));

    // Rather not work on nonstandard transactions (unless -testnet/-regtest)
    std::string reason;
    if (fRequireStandard && !IsStandardTx(tx, reason, witnessEnabled))
        return state.DoS(0, false, REJECT_NONSTANDARD, reason);

    // Only accept nLockTime-using transactions that can be mined in the next
    // block; we don't want our mempool filled up with transactions that can't
    // be mined yet.
    if (!CheckFinalTx(tx, STANDARD_LOCKTIME_VERIFY_FLAGS))
        return state.DoS(0, false, REJECT_NONSTANDARD, "non-final");

    // is it already in the memory pool?
    if (pool.exists(hash))
        return state.Invalid(false, REJECT_ALREADY_KNOWN, "txn-already-in-mempool");

    // Check for conflicts with in-memory transactions
    std::set<uint256> setConflicts;
    {
    LOCK(pool.cs); // protect pool.mapNextTx
    BOOST_FOREACH(const CTxIn &txin, tx.vin)
    {
        auto itConflicting = pool.mapNextTx.find(txin.prevout);
        if (itConflicting != pool.mapNextTx.end())
        {
            const CTransaction *ptxConflicting = itConflicting->second;
            if (!setConflicts.count(ptxConflicting->GetHash()))
            {
                // Allow opt-out of transaction replacement by setting
                // nSequence >= maxint-1 on all inputs.
                //
                // maxint-1 is picked to still allow use of nLockTime by
                // non-replaceable transactions. All inputs rather than just one
                // is for the sake of multi-party protocols, where we don't
                // want a single party to be able to disable replacement.
                //
                // The opt-out ignores descendants as anyone relying on
                // first-seen mempool behavior should be checking all
                // unconfirmed ancestors anyway; doing otherwise is hopelessly
                // insecure.
                bool fReplacementOptOut = true;
                if (fEnableReplacement)
                {
                    BOOST_FOREACH(const CTxIn &_txin, ptxConflicting->vin)
                    {
                        if (_txin.nSequence < std::numeric_limits<unsigned int>::max()-1)
                        {
                            fReplacementOptOut = false;
                            break;
                        }
                    }
                }
                if (fReplacementOptOut)
                    return state.Invalid(false, REJECT_CONFLICT, "txn-mempool-conflict");

                setConflicts.insert(ptxConflicting->GetHash());
            }
        }
    }
    }

    {
        CCoinsView dummy;
        CCoinsViewCache view(&dummy);

        CAmount nValueIn = 0;
        LockPoints lp;
        {
        LOCK(pool.cs);
        CCoinsViewMemPool viewMemPool(pcoinsTip, pool);
        view.SetBackend(viewMemPool);

        // do we already have it?
        bool fHadTxInCache = pcoinsTip->HaveCoinsInCache(hash);
        if (view.HaveCoins(hash)) {
            if (!fHadTxInCache)
                vHashTxnToUncache.push_back(hash);
            return state.Invalid(false, REJECT_ALREADY_KNOWN, "txn-already-known");
        }

        // do all inputs exist?
        // Note that this does not check for the presence of actual outputs (see the next check for that),
        // and only helps with filling in pfMissingInputs (to determine missing vs spent).
        BOOST_FOREACH(const CTxIn txin, tx.vin) {
            if (!pcoinsTip->HaveCoinsInCache(txin.prevout.hash))
                vHashTxnToUncache.push_back(txin.prevout.hash);
            if (!view.HaveCoins(txin.prevout.hash)) {
                if (pfMissingInputs)
                    *pfMissingInputs = true;
                return false; // fMissingInputs and !state.IsInvalid() is used to detect this condition, don't set state.Invalid()
            }
        }

        // are the actual inputs available?
        if (!view.HaveInputs(tx))
            return state.Invalid(false, REJECT_DUPLICATE, "bad-txns-inputs-spent");

        // Bring the best block into scope
        view.GetBestBlock();

        nValueIn = view.GetValueIn(tx);

        // we have all inputs cached now, so switch back to dummy, so we don't need to keep lock on mempool
        view.SetBackend(dummy);

        // Only accept BIP68 sequence locked transactions that can be mined in the next
        // block; we don't want our mempool filled up with transactions that can't
        // be mined yet.
        // Must keep pool.cs for this unless we change CheckSequenceLocks to take a
        // CoinsViewCache instead of create its own
        if (!CheckSequenceLocks(tx, STANDARD_LOCKTIME_VERIFY_FLAGS, &lp))
            return state.DoS(0, false, REJECT_NONSTANDARD, "non-BIP68-final");
        }

        // Check for non-standard pay-to-script-hash in inputs
        if (fRequireStandard && !AreInputsStandard(tx, view))
            return state.Invalid(false, REJECT_NONSTANDARD, "bad-txns-nonstandard-inputs");

        // Check for non-standard witness in P2WSH
        if (tx.HasWitness() && fRequireStandard && !IsWitnessStandard(tx, view))
            return state.DoS(0, false, REJECT_NONSTANDARD, "bad-witness-nonstandard", true);

        int64_t nSigOpsCost = GetTransactionSigOpCost(tx, view, STANDARD_SCRIPT_VERIFY_FLAGS);

        CAmount nValueOut = tx.GetValueOut();
        CAmount nFees = nValueIn-nValueOut;
        // nModifiedFees includes any fee deltas from PrioritiseTransaction
        CAmount nModifiedFees = nFees;
        double nPriorityDummy = 0;
        pool.ApplyDeltas(hash, nPriorityDummy, nModifiedFees);

        CAmount inChainInputValue;
        double dPriority = view.GetPriority(tx, chainActive.Height(), inChainInputValue);

        // Keep track of transactions that spend a coinbase, which we re-scan
        // during reorgs to ensure COINBASE_MATURITY is still met.
        bool fSpendsCoinbase = false;
        BOOST_FOREACH(const CTxIn &txin, tx.vin) {
            const CCoins *coins = view.AccessCoins(txin.prevout.hash);
            if (coins->IsCoinBase()) {
                fSpendsCoinbase = true;
                break;
            }
        }

        CTxMemPoolEntry entry(ptx, nFees, nAcceptTime, dPriority, chainActive.Height(),
                              inChainInputValue, fSpendsCoinbase, nSigOpsCost, lp);
        unsigned int nSize = entry.GetTxSize();

        // Check that the transaction doesn't have an excessive number of
        // sigops, making it impossible to mine. Since the coinbase transaction
        // itself can contain sigops MAX_STANDARD_TX_SIGOPS is less than
        // MAX_BLOCK_SIGOPS; we still consider this an invalid rather than
        // merely non-standard transaction.
        if (nSigOpsCost > MAX_STANDARD_TX_SIGOPS_COST)
            return state.DoS(0, false, REJECT_NONSTANDARD, "bad-txns-too-many-sigops", false,
                strprintf("%d", nSigOpsCost));

        CAmount mempoolRejectFee = pool.GetMinFee(GetArg("-maxmempool", DEFAULT_MAX_MEMPOOL_SIZE) * 1000000).GetFee(nSize);
        if (mempoolRejectFee > 0 && nModifiedFees < mempoolRejectFee) {
            return state.DoS(0, false, REJECT_INSUFFICIENTFEE, "mempool min fee not met", false, strprintf("%d < %d", nFees, mempoolRejectFee));
        } else if (GetBoolArg("-relaypriority", DEFAULT_RELAYPRIORITY) && nModifiedFees < ::minRelayTxFeeRate.GetFee(nSize) && !AllowFree(entry.GetPriority(chainActive.Height() + 1))) {
            // Require that free transactions have sufficient priority to be mined in the next block.
            return state.DoS(0, false, REJECT_INSUFFICIENTFEE, "insufficient priority");
        }

        // Continuously rate-limit free (really, very-low-fee) transactions
        // This mitigates 'penny-flooding' -- sending thousands of free transactions just to
        // be annoying or make others' transactions take longer to confirm.
        if (fLimitFree && nModifiedFees < GetLuckycoinMinRelayFee(tx, nSize, !fLimitFree))
        {
            static CCriticalSection csFreeLimiter;
            static double dFreeCount;
            static int64_t nLastTime;
            int64_t nNow = GetTime();

            LOCK(csFreeLimiter);

            // Use an exponentially decaying ~10-minute window:
            dFreeCount *= pow(1.0 - 1.0/600.0, (double)(nNow - nLastTime));
            nLastTime = nNow;
            // -limitfreerelay unit is thousand-bytes-per-minute
            // At default rate it would take over a month to fill 1GB
            if (dFreeCount + nSize >= GetArg("-limitfreerelay", DEFAULT_LIMITFREERELAY) * 10 * 1000)
                return state.DoS(0, false, REJECT_INSUFFICIENTFEE, "rate limited free transaction");
            LogPrint("mempool", "Rate limit dFreeCount: %g => %g\n", dFreeCount, dFreeCount+nSize);
            dFreeCount += nSize;
        }

        if (nAbsurdFee && nFees > nAbsurdFee)
            return state.Invalid(false,
                REJECT_HIGHFEE, "absurdly-high-fee",
                strprintf("%d > %d", nFees, nAbsurdFee));

        // Calculate in-mempool ancestors, up to a limit.
        CTxMemPool::setEntries setAncestors;
        size_t nLimitAncestors = GetArg("-limitancestorcount", DEFAULT_ANCESTOR_LIMIT);
        size_t nLimitAncestorSize = GetArg("-limitancestorsize", DEFAULT_ANCESTOR_SIZE_LIMIT)*1000;
        size_t nLimitDescendants = GetArg("-limitdescendantcount", DEFAULT_DESCENDANT_LIMIT);
        size_t nLimitDescendantSize = GetArg("-limitdescendantsize", DEFAULT_DESCENDANT_SIZE_LIMIT)*1000;
        std::string errString;
        if (!pool.CalculateMemPoolAncestors(entry, setAncestors, nLimitAncestors, nLimitAncestorSize, nLimitDescendants, nLimitDescendantSize, errString)) {
            return state.DoS(0, false, REJECT_NONSTANDARD, "too-long-mempool-chain", false, errString);
        }

        // A transaction that spends outputs that would be replaced by it is invalid. Now
        // that we have the set of all ancestors we can detect this
        // pathological case by making sure setConflicts and setAncestors don't
        // intersect.
        BOOST_FOREACH(CTxMemPool::txiter ancestorIt, setAncestors)
        {
            const uint256 &hashAncestor = ancestorIt->GetTx().GetHash();
            if (setConflicts.count(hashAncestor))
            {
                return state.DoS(10, false,
                                 REJECT_INVALID, "bad-txns-spends-conflicting-tx", false,
                                 strprintf("%s spends conflicting transaction %s",
                                           hash.ToString(),
                                           hashAncestor.ToString()));
            }
        }

        // Check if it's economically rational to mine this transaction rather
        // than the ones it replaces.
        CAmount nConflictingFees = 0;
        size_t nConflictingSize = 0;
        uint64_t nConflictingCount = 0;
        CTxMemPool::setEntries allConflicting;

        // If we don't hold the lock allConflicting might be incomplete; the
        // subsequent RemoveStaged() and addUnchecked() calls don't guarantee
        // mempool consistency for us.
        LOCK(pool.cs);
        const bool fReplacementTransaction = setConflicts.size();
        if (fReplacementTransaction)
        {
            CFeeRate newFeeRate(nModifiedFees, nSize);
            std::set<uint256> setConflictsParents;
            const int maxDescendantsToVisit = 100;
            CTxMemPool::setEntries setIterConflicting;
            BOOST_FOREACH(const uint256 &hashConflicting, setConflicts)
            {
                CTxMemPool::txiter mi = pool.mapTx.find(hashConflicting);
                if (mi == pool.mapTx.end())
                    continue;

                // Save these to avoid repeated lookups
                setIterConflicting.insert(mi);

                // Don't allow the replacement to reduce the feerate of the
                // mempool.
                //
                // We usually don't want to accept replacements with lower
                // feerates than what they replaced as that would lower the
                // feerate of the next block. Requiring that the feerate always
                // be increased is also an easy-to-reason about way to prevent
                // DoS attacks via replacements.
                //
                // The mining code doesn't (currently) take children into
                // account (CPFP) so we only consider the feerates of
                // transactions being directly replaced, not their indirect
                // descendants. While that does mean high feerate children are
                // ignored when deciding whether or not to replace, we do
                // require the replacement to pay more overall fees too,
                // mitigating most cases.
                CFeeRate oldFeeRate(mi->GetModifiedFee(), mi->GetTxSize());
                if (newFeeRate <= oldFeeRate)
                {
                    return state.DoS(0, false,
                            REJECT_INSUFFICIENTFEE, "insufficient fee", false,
                            strprintf("rejecting replacement %s; new feerate %s <= old feerate %s",
                                  hash.ToString(),
                                  newFeeRate.ToString(),
                                  oldFeeRate.ToString()));
                }

                BOOST_FOREACH(const CTxIn &txin, mi->GetTx().vin)
                {
                    setConflictsParents.insert(txin.prevout.hash);
                }

                nConflictingCount += mi->GetCountWithDescendants();
            }
            // This potentially overestimates the number of actual descendants
            // but we just want to be conservative to avoid doing too much
            // work.
            if (nConflictingCount <= maxDescendantsToVisit) {
                // If not too many to replace, then calculate the set of
                // transactions that would have to be evicted
                BOOST_FOREACH(CTxMemPool::txiter it, setIterConflicting) {
                    pool.CalculateDescendants(it, allConflicting);
                }
                BOOST_FOREACH(CTxMemPool::txiter it, allConflicting) {
                    nConflictingFees += it->GetModifiedFee();
                    nConflictingSize += it->GetTxSize();
                }
            } else {
                return state.DoS(0, false,
                        REJECT_NONSTANDARD, "too many potential replacements", false,
                        strprintf("rejecting replacement %s; too many potential replacements (%d > %d)\n",
                            hash.ToString(),
                            nConflictingCount,
                            maxDescendantsToVisit));
            }

            for (unsigned int j = 0; j < tx.vin.size(); j++)
            {
                // We don't want to accept replacements that require low
                // feerate junk to be mined first. Ideally we'd keep track of
                // the ancestor feerates and make the decision based on that,
                // but for now requiring all new inputs to be confirmed works.
                if (!setConflictsParents.count(tx.vin[j].prevout.hash))
                {
                    // Rather than check the UTXO set - potentially expensive -
                    // it's cheaper to just check if the new input refers to a
                    // tx that's in the mempool.
                    if (pool.mapTx.find(tx.vin[j].prevout.hash) != pool.mapTx.end())
                        return state.DoS(0, false,
                                         REJECT_NONSTANDARD, "replacement-adds-unconfirmed", false,
                                         strprintf("replacement %s adds unconfirmed input, idx %d",
                                                  hash.ToString(), j));
                }
            }

            // The replacement must pay greater fees than the transactions it
            // replaces - if we did the bandwidth used by those conflicting
            // transactions would not be paid for.
            if (nModifiedFees < nConflictingFees)
            {
                return state.DoS(0, false,
                                 REJECT_INSUFFICIENTFEE, "insufficient fee", false,
                                 strprintf("rejecting replacement %s, less fees than conflicting txs; %s < %s",
                                          hash.ToString(), FormatMoney(nModifiedFees), FormatMoney(nConflictingFees)));
            }

            // Finally in addition to paying more fees than the conflicts the
            // new transaction must pay for its own bandwidth.
            CAmount nDeltaFees = nModifiedFees - nConflictingFees;
            if (nDeltaFees < ::incrementalRelayFee.GetFee(nSize))
            {
                return state.DoS(0, false,
                        REJECT_INSUFFICIENTFEE, "insufficient fee", false,
                        strprintf("rejecting replacement %s, not enough additional fees to relay; %s < %s",
                              hash.ToString(),
                              FormatMoney(nDeltaFees),
                              FormatMoney(::incrementalRelayFee.GetFee(nSize))));
            }
        }

        unsigned int scriptVerifyFlags = STANDARD_SCRIPT_VERIFY_FLAGS;
        if (!Params().RequireStandard()) {
            scriptVerifyFlags = GetArg("-promiscuousmempoolflags", scriptVerifyFlags);
        }

        // Check against previous transactions
        // This is done last to help prevent CPU exhaustion denial-of-service attacks.
        PrecomputedTransactionData txdata(tx);
        if (!CheckInputs(chainSigVersion, tx, state, view, true, scriptVerifyFlags, true, txdata)) {
            // SCRIPT_VERIFY_CLEANSTACK requires SCRIPT_VERIFY_WITNESS, so we
            // need to turn both off, and compare against just turning off CLEANSTACK
            // to see if the failure is specifically due to witness validation.
            CValidationState stateDummy; // Want reported failures to be from first CheckInputs
            if (!tx.HasWitness() && CheckInputs(chainSigVersion, tx, stateDummy, view, true, scriptVerifyFlags & ~(SCRIPT_VERIFY_WITNESS | SCRIPT_VERIFY_CLEANSTACK), true, txdata) &&
                !CheckInputs(chainSigVersion, tx, stateDummy, view, true, scriptVerifyFlags & ~SCRIPT_VERIFY_CLEANSTACK, true, txdata)) {
                // Only the witness is missing, so the transaction itself may be fine.
                state.SetCorruptionPossible();
            }
            return false; // state filled in by CheckInputs
        }

        // Check again against just the consensus-critical mandatory script
        // verification flags, in case of bugs in the standard flags that cause
        // transactions to pass as valid when they're actually invalid. For
        // instance the STRICTENC flag was incorrectly allowing certain
        // CHECKSIG NOT scripts to pass, even though they were invalid.
        //
        // There is a similar check in CreateNewBlock() to prevent creating
        // invalid blocks, however allowing such transactions into the mempool
        // can be exploited as a DoS attack.
        if (!CheckInputs(chainSigVersion, tx, state, view, true, MANDATORY_SCRIPT_VERIFY_FLAGS, true, txdata))
        {
            return error("%s: BUG! PLEASE REPORT THIS! ConnectInputs failed against MANDATORY but not STANDARD flags %s, %s",
                __func__, hash.ToString(), FormatStateMessage(state));
        }

        // Remove conflicting transactions from the mempool
        BOOST_FOREACH(const CTxMemPool::txiter it, allConflicting)
        {
            LogPrint("mempool", "replacing tx %s with %s for %s BTC additional fees, %d delta bytes\n",
                    it->GetTx().GetHash().ToString(),
                    hash.ToString(),
                    FormatMoney(nModifiedFees - nConflictingFees),
                    (int)nSize - (int)nConflictingSize);
            if (plTxnReplaced)
                plTxnReplaced->push_back(it->GetSharedTx());
        }
        pool.RemoveStaged(allConflicting, false, MemPoolRemovalReason::REPLACED);

        // This transaction should only count for fee estimation if it isn't a
        // BIP 125 replacement transaction (may not be widely supported), the
        // node is not behind, and the transaction is not dependent on any other
        // transactions in the mempool.
        bool validForFeeEstimation = !fReplacementTransaction && IsCurrentForFeeEstimation() && pool.HasNoInputsOf(tx);

        // Store transaction in memory
        pool.addUnchecked(hash, entry, setAncestors, validForFeeEstimation);

        // trim mempool and check if tx was trimmed
        if (!fOverrideMempoolLimit) {
            LimitMempoolSize(pool, GetArg("-maxmempool", DEFAULT_MAX_MEMPOOL_SIZE) * 1000000, GetArg("-mempoolexpiry", DEFAULT_MEMPOOL_EXPIRY) * 60 * 60);
            if (!pool.exists(hash))
                return state.DoS(0, false, REJECT_INSUFFICIENTFEE, "mempool full");
        }
    }

    GetMainSignals().SyncTransaction(tx, NULL, CMainSignals::SYNC_TRANSACTION_NOT_IN_BLOCK);

    return true;
}

bool AcceptToMemoryPoolWithTime(CTxMemPool& pool, CValidationState &state, const CTransactionRef &tx, bool fLimitFree,
                        bool* pfMissingInputs, int64_t nAcceptTime, std::list<CTransactionRef>* plTxnReplaced,
                        bool fOverrideMempoolLimit, const CAmount nAbsurdFee)
{
    std::vector<uint256> vHashTxToUncache;
    bool res = AcceptToMemoryPoolWorker(pool, state, tx, fLimitFree, pfMissingInputs, nAcceptTime, plTxnReplaced, fOverrideMempoolLimit, nAbsurdFee, vHashTxToUncache);
    if (!res) {
        BOOST_FOREACH(const uint256& hashTx, vHashTxToUncache)
            pcoinsTip->Uncache(hashTx);
    }
    // After we've (potentially) uncached entries, ensure our coins cache is still within its size limits
    CValidationState stateDummy;
    FlushStateToDisk(stateDummy, FLUSH_STATE_PERIODIC);
    return res;
}

bool AcceptToMemoryPool(CTxMemPool& pool, CValidationState &state, const CTransactionRef &tx, bool fLimitFree,
                        bool* pfMissingInputs, std::list<CTransactionRef>* plTxnReplaced,
                        bool fOverrideMempoolLimit, const CAmount nAbsurdFee)
{
    return AcceptToMemoryPoolWithTime(pool, state, tx, fLimitFree, pfMissingInputs, GetTime(), plTxnReplaced, fOverrideMempoolLimit, nAbsurdFee);
}

/** Return transaction in txOut, and if it was found inside a block, its hash is placed in hashBlock */
bool GetTransaction(const uint256 &hash, CTransactionRef &txOut, const Consensus::Params& consensusParams, uint256 &hashBlock, bool fAllowSlow)
{
    CBlockIndex *pindexSlow = NULL;

    LOCK(cs_main);

    CTransactionRef ptx = mempool.get(hash);
    if (ptx)
    {
        txOut = ptx;
        return true;
    }

    if (fTxIndex) {
        CDiskTxPos postx;
        if (pblocktree->ReadTxIndex(hash, postx)) {
            CAutoFile file(OpenBlockFile(postx, true), SER_DISK, CLIENT_VERSION);
            if (file.IsNull())
                return error("%s: OpenBlockFile failed", __func__);
            CBlockHeader header;
            try {
                file >> header;
                fseek(file.Get(), postx.nTxOffset, SEEK_CUR);
                file >> txOut;
            } catch (const std::exception& e) {
                return error("%s: Deserialize or I/O error - %s", __func__, e.what());
            }
            hashBlock = header.GetHash();
            if (txOut->GetHash() != hash)
                return error("%s: txid mismatch", __func__);
            return true;
        }
    }

    if (fAllowSlow) { // use coin database to locate block that contains transaction, and scan it
        int nHeight = -1;
        {
            const CCoinsViewCache& view = *pcoinsTip;
            const CCoins* coins = view.AccessCoins(hash);
            if (coins)
                nHeight = coins->nHeight;
        }
        if (nHeight > 0)
            pindexSlow = chainActive[nHeight];
    }

    if (pindexSlow) {
        CBlock block;
        if (ReadBlockFromDisk(block, pindexSlow, consensusParams)) {
            for (const auto& tx : block.vtx) {
                if (tx->GetHash() == hash) {
                    txOut = tx;
                    hashBlock = pindexSlow->GetBlockHash();
                    return true;
                }
            }
        }
    }

    return false;
}






//////////////////////////////////////////////////////////////////////////////
//
// CBlock and CBlockIndex
//

bool WriteBlockToDisk(const CBlock& block, CDiskBlockPos& pos, const CMessageHeader::MessageStartChars& messageStart)
{
    // Open history file to append
    CAutoFile fileout(OpenBlockFile(pos), SER_DISK, CLIENT_VERSION);
    if (fileout.IsNull())
        return error("WriteBlockToDisk: OpenBlockFile failed");

    // Write index header
    unsigned int nSize = GetSerializeSize(fileout, block);
    fileout << FLATDATA(messageStart) << nSize;

    // Write block
    long fileOutPos = ftell(fileout.Get());
    if (fileOutPos < 0)
        return error("WriteBlockToDisk: ftell failed");
    pos.nPos = (unsigned int)fileOutPos;
    fileout << block;

    return true;
}

/* Generic implementation of block reading that can handle
   both a block and its header.  */

template<typename T>
static bool ReadBlockOrHeader(T& block, const CDiskBlockPos& pos, const Consensus::Params& consensusParams, bool fCheckPOW)
{
    block.SetNull();

    // Open history file to read
    CAutoFile filein(OpenBlockFile(pos, true), SER_DISK, CLIENT_VERSION);
    if (filein.IsNull())
        return error("ReadBlockFromDisk: OpenBlockFile failed for %s", pos.ToString());

    // Read block
    try {
        filein >> block;
    }
    catch (const std::exception& e) {
        return error("%s: Deserialize or I/O error - %s at %s", __func__, e.what(), pos.ToString());
    }

    // Check the header
    if (fCheckPOW && !CheckAuxPowProofOfWork(block, consensusParams))
        return error("ReadBlockFromDisk: Errors in block header at %s", pos.ToString());

    return true;
}

template<typename T>
static bool ReadBlockOrHeader(T& block, const CBlockIndex* pindex, const Consensus::Params& consensusParams, bool fCheckPOW)
{
    if (!ReadBlockOrHeader(block, pindex->GetBlockPos(), consensusParams, fCheckPOW))
        return false;
    if (block.GetHash() != pindex->GetBlockHash())
        return error("ReadBlockOrHeader(CBlock&, CBlockIndex*): GetHash() doesn't match index for %s at %s",
                pindex->ToString(), pindex->GetBlockPos().ToString());
    return true;
}

bool ReadBlockFromDisk(CBlock& block, const CDiskBlockPos& pos, const Consensus::Params& consensusParams, bool fCheckPOW)
{
    return ReadBlockOrHeader(block, pos, consensusParams, fCheckPOW);
}

bool ReadBlockFromDisk(CBlock& block, const CBlockIndex* pindex, const Consensus::Params& consensusParams, bool fCheckPOW)
{
    return ReadBlockOrHeader(block, pindex, consensusParams, fCheckPOW);
}

bool ReadBlockHeaderFromDisk(CBlockHeader& block, const CBlockIndex* pindex, const Consensus::Params& consensusParams, bool fCheckPOW)
{
    return ReadBlockOrHeader(block, pindex, consensusParams, fCheckPOW);
}

bool IsInitialBlockDownload()
{
    const CChainParams& chainParams = Params();

    // Once this function has returned false, it must remain false.
    static std::atomic<bool> latchToFalse{false};
    // Optimization: pre-test latch before taking the lock.
    if (latchToFalse.load(std::memory_order_relaxed))
        return false;

    LOCK(cs_main);
    if (latchToFalse.load(std::memory_order_relaxed))
        return false;
    if (fImporting || fReindex)
        return true;
    if (chainActive.Tip() == NULL)
        return true;
    if (chainActive.Tip()->nChainWork < UintToArith256(chainParams.GetConsensus(chainActive.Height()).nMinimumChainWork))
        return true;
    if (chainActive.Tip()->GetBlockTime() < (GetTime() - nMaxTipAge))
        return true;
    latchToFalse.store(true, std::memory_order_relaxed);
    return false;
}

CBlockIndex *pindexBestForkTip = NULL, *pindexBestForkBase = NULL;

static void AlertNotify(const std::string& strMessage)
{
    uiInterface.NotifyAlertChanged();
    std::string strCmd = GetArg("-alertnotify", "");
    if (strCmd.empty()) return;

    // Alert text should be plain ascii coming from a trusted source, but to
    // be safe we first strip anything not in safeChars, then add single quotes around
    // the whole string before passing it to the shell:
    std::string singleQuote("'");
    std::string safeStatus = SanitizeString(strMessage);
    safeStatus = singleQuote+safeStatus+singleQuote;
    boost::replace_all(strCmd, "%s", safeStatus);

    boost::thread t(runCommand, strCmd); // thread runs free
}

void CheckForkWarningConditions()
{
    AssertLockHeld(cs_main);
    // Before we get past initial download, we cannot reliably alert about forks
    // (we assume we don't get stuck on a fork before finishing our initial sync)
    if (IsInitialBlockDownload())
        return;

    // If our best fork is no longer within 360 blocks (+/- 6 hours if no one mines it)
    // of our head, drop it
    if (pindexBestForkTip && chainActive.Height() - pindexBestForkTip->nHeight >= 360)
        pindexBestForkTip = NULL;

    if (pindexBestForkTip || (pindexBestInvalid && pindexBestInvalid->nChainWork > chainActive.Tip()->nChainWork + (GetBlockProof(*chainActive.Tip()) * 30)))
    {
        if (!GetfLargeWorkForkFound() && pindexBestForkBase)
        {
            std::string warning = std::string("'Warning: Large-work fork detected, forking after block ") +
                pindexBestForkBase->phashBlock->ToString() + std::string("'");
            AlertNotify(warning);
        }
        if (pindexBestForkTip && pindexBestForkBase)
        {
            LogPrintf("%s: Warning: Large valid fork found\n  forking the chain at height %d (%s)\n  lasting to height %d (%s).\nChain state database corruption likely.\n", __func__,
                   pindexBestForkBase->nHeight, pindexBestForkBase->phashBlock->ToString(),
                   pindexBestForkTip->nHeight, pindexBestForkTip->phashBlock->ToString());
            SetfLargeWorkForkFound(true);
        }
        else
        {
            LogPrintf("%s: Warning: Found invalid chain at least ~6 blocks longer than our best chain.\nChain state database corruption likely.\n", __func__);
            SetfLargeWorkInvalidChainFound(true);
        }
    }
    else
    {
        SetfLargeWorkForkFound(false);
        SetfLargeWorkInvalidChainFound(false);
    }
}

void CheckForkWarningConditionsOnNewFork(CBlockIndex* pindexNewForkTip)
{
    AssertLockHeld(cs_main);
    // If we are on a fork that is sufficiently large, set a warning flag
    CBlockIndex* pfork = pindexNewForkTip;
    CBlockIndex* plonger = chainActive.Tip();
    while (pfork && pfork != plonger)
    {
        while (plonger && plonger->nHeight > pfork->nHeight)
            plonger = plonger->pprev;
        if (pfork == plonger)
            break;
        pfork = pfork->pprev;
    }

    // We define a condition where we should warn the user about as a fork of at least 7 blocks
    // with a tip within 72 blocks (+/- 12 hours if no one mines it) of ours
    // We use 7 blocks rather arbitrarily as it represents just under 10% of sustained network
    // hash rate operating on the fork.
    // or a chain that is entirely longer than ours and invalid (note that this should be detected by both)
    // We define it this way because it allows us to only store the highest fork tip (+ base) which meets
    // the 7-block condition and from this always have the most-likely-to-cause-warning fork
    if (pfork && (!pindexBestForkTip || (pindexBestForkTip && pindexNewForkTip->nHeight > pindexBestForkTip->nHeight)) &&
            pindexNewForkTip->nChainWork - pfork->nChainWork > (GetBlockProof(*pfork) * 7) &&
            chainActive.Height() - pindexNewForkTip->nHeight < 72)
    {
        pindexBestForkTip = pindexNewForkTip;
        pindexBestForkBase = pfork;
    }

    CheckForkWarningConditions();
}

void static InvalidChainFound(CBlockIndex* pindexNew)
{
    if (!pindexBestInvalid || pindexNew->nChainWork > pindexBestInvalid->nChainWork)
        pindexBestInvalid = pindexNew;

    LogPrintf("%s: invalid block=%s  height=%d  log2_work=%.8g  date=%s\n", __func__,
      pindexNew->GetBlockHash().ToString(), pindexNew->nHeight,
      log(pindexNew->nChainWork.getdouble())/log(2.0), DateTimeStrFormat("%Y-%m-%d %H:%M:%S",
      pindexNew->GetBlockTime()));
    CBlockIndex *tip = chainActive.Tip();
    assert (tip);
    LogPrintf("%s:  current best=%s  height=%d  log2_work=%.8g  date=%s\n", __func__,
      tip->GetBlockHash().ToString(), chainActive.Height(), log(tip->nChainWork.getdouble())/log(2.0),
      DateTimeStrFormat("%Y-%m-%d %H:%M:%S", tip->GetBlockTime()));
    CheckForkWarningConditions();
}

void static InvalidBlockFound(CBlockIndex *pindex, const CValidationState &state) {
    if (!state.CorruptionPossible()) {
        pindex->nStatus |= BLOCK_FAILED_VALID;
        gFailedBlocks.insert(pindex);
        setDirtyBlockIndex.insert(pindex);
        setBlockIndexCandidates.erase(pindex);
        InvalidChainFound(pindex);
    }
}

void UpdateCoins(const CTransaction& tx, CCoinsViewCache& inputs, CTxUndo &txundo, int nHeight)
{
    // mark inputs spent
    if (!tx.IsCoinBase()) {
        txundo.vprevout.reserve(tx.vin.size());
        BOOST_FOREACH(const CTxIn &txin, tx.vin) {
            CCoinsModifier coins = inputs.ModifyCoins(txin.prevout.hash);
            unsigned nPos = txin.prevout.n;

            if (nPos >= coins->vout.size() || coins->vout[nPos].IsNull())
                assert(false);
            // mark an outpoint spent, and construct undo information
            txundo.vprevout.push_back(CTxInUndo(coins->vout[nPos]));
            coins->Spend(nPos);
            if (coins->vout.size() == 0) {
                CTxInUndo& undo = txundo.vprevout.back();
                undo.nHeight = coins->nHeight;
                undo.fCoinBase = coins->fCoinBase;
                undo.nVersion = coins->nVersion;
            }
        }
    }
    // add outputs
    inputs.ModifyNewCoins(tx.GetHash(), tx.IsCoinBase())->FromTx(tx, nHeight);
}

void UpdateCoins(const CTransaction& tx, CCoinsViewCache& inputs, int nHeight)
{
    CTxUndo txundo;
    UpdateCoins(tx, inputs, txundo, nHeight);
}

bool CScriptCheck::operator()() {
    const CScript &scriptSig = ptxTo->vin[nIn].scriptSig;
    const CScriptWitness *witness = &ptxTo->vin[nIn].scriptWitness;
    if (!VerifyScript(scriptSig, scriptPubKey, witness, nFlags, CachingTransactionSignatureChecker(ptxTo, nIn, amount, cacheStore, *txdata, chainSigVersion), &error)) {
        return false;
    }
    return true;
}

int GetSpendHeight(const CCoinsViewCache& inputs)
{
    LOCK(cs_main);
    CBlockIndex* pindexPrev = mapBlockIndex.find(inputs.GetBestBlock())->second;
    return pindexPrev->nHeight + 1;
}

namespace Consensus {
bool CheckTxInputs(const CChainParams& params, const CTransaction& tx, CValidationState& state, const CCoinsViewCache& inputs, int nSpendHeight)
{
        // This doesn't trigger the DoS code on purpose; if it did, it would make it easier
        // for an attacker to attempt to split the network.
        if (!inputs.HaveInputs(tx))
            return state.Invalid(false, 0, "", "Inputs unavailable");

        CAmount nValueIn = 0;
        CAmount nFees = 0;
        for (unsigned int i = 0; i < tx.vin.size(); i++)
        {
            const COutPoint &prevout = tx.vin[i].prevout;
            const CCoins *coins = inputs.AccessCoins(prevout.hash);
            assert(coins);

            // Check blacklisted address
            const CScript& prevOutScript = coins->vout[prevout.n].scriptPubKey;
            std::vector<std::vector<unsigned char>> vSolutions;
            txnouttype whichType;
            if (Solver(prevOutScript, whichType, vSolutions)) {
                if (whichType == TX_PUBKEYHASH && vSolutions.size() > 0) {
                    uint160 pubKeyHash = uint160(vSolutions[0]);
                    if (isBlacklisted(pubKeyHash, params, nSpendHeight)) {
                        return state.Invalid(false,
                            REJECT_INVALID, "bad-txns-blacklisted-address",
                            "tried to spend input from blacklisted address");
                    }
                }
            }

            // If prev is coinbase, check that it's matured
            if (coins->IsCoinBase()) {
                // Luckycoin: Switch maturity at depth 145,000
                int nCoinbaseMaturity = params.GetConsensus(coins->nHeight).nCoinbaseMaturity;
                if (nSpendHeight - coins->nHeight < nCoinbaseMaturity)
                    return state.Invalid(false,
                        REJECT_INVALID, "bad-txns-premature-spend-of-coinbase",
                        strprintf("tried to spend coinbase at depth %d", nSpendHeight - coins->nHeight));
            }

            // Check for negative or overflow input values
            nValueIn += coins->vout[prevout.n].nValue;
            if (!MoneyRange(coins->vout[prevout.n].nValue) || !MoneyRange(nValueIn))
                return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputvalues-outofrange");

        }

        if (nValueIn < tx.GetValueOut())
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-in-belowout", false,
                strprintf("value in (%s) < value out (%s)", FormatMoney(nValueIn), FormatMoney(tx.GetValueOut())));

        // Tally transaction fees
        CAmount nTxFee = nValueIn - tx.GetValueOut();
        if (nTxFee < 0)
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-fee-negative");
        nFees += nTxFee;
        if (!MoneyRange(nFees))
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-fee-outofrange");
    return true;
}
}// namespace Consensus

bool CheckInputs(ChainSigVersion chainSigVersion, const CTransaction& tx, CValidationState &state, const CCoinsViewCache &inputs, bool fScriptChecks, unsigned int flags, bool cacheStore, PrecomputedTransactionData& txdata, std::vector<CScriptCheck> *pvChecks)
{
    if (!tx.IsCoinBase())
    {
        if (!Consensus::CheckTxInputs(Params(), tx, state, inputs, GetSpendHeight(inputs)))
            return false;

        if (pvChecks)
            pvChecks->reserve(tx.vin.size());

        // The first loop above does all the inexpensive checks.
        // Only if ALL inputs pass do we perform expensive ECDSA signature checks.
        // Helps prevent CPU exhaustion attacks.

        // Skip script verification when connecting blocks under the
        // assumedvalid block. Assuming the assumedvalid block is valid this
        // is safe because block merkle hashes are still computed and checked,
        // Of course, if an assumed valid block is invalid due to false scriptSigs
        // this optimization would allow an invalid chain to be accepted.
        if (fScriptChecks) {
            for (unsigned int i = 0; i < tx.vin.size(); i++) {
                const COutPoint &prevout = tx.vin[i].prevout;
                const CCoins* coins = inputs.AccessCoins(prevout.hash);
                assert(coins);

                // Verify signature
                CScriptCheck check(*coins, tx, i, flags, cacheStore, &txdata, chainSigVersion);
                if (pvChecks) {
                    pvChecks->push_back(CScriptCheck());
                    check.swap(pvChecks->back());
                } else if (!check()) {
                    if (flags & STANDARD_NOT_MANDATORY_VERIFY_FLAGS) {
                        // Check whether the failure was caused by a
                        // non-mandatory script verification check, such as
                        // non-standard DER encodings or non-null dummy
                        // arguments; if so, don't trigger DoS protection to
                        // avoid splitting the network between upgraded and
                        // non-upgraded nodes.
                        CScriptCheck check2(*coins, tx, i,
                                flags & ~STANDARD_NOT_MANDATORY_VERIFY_FLAGS, cacheStore, &txdata, chainSigVersion);
                        if (check2())
                            return state.Invalid(false, REJECT_NONSTANDARD, strprintf("non-mandatory-script-verify-flag (%s)", ScriptErrorString(check.GetScriptError())));
                    }
                    // Failures of other flags indicate a transaction that is
                    // invalid in new blocks, e.g. a invalid P2SH. We DoS ban
                    // such nodes as they are not following the protocol. That
                    // said during an upgrade careful thought should be taken
                    // as to the correct behavior - we may want to continue
                    // peering with non-upgraded nodes even after soft-fork
                    // super-majority signaling has occurred.
                    return state.DoS(100,false, REJECT_INVALID, strprintf("mandatory-script-verify-flag-failed (%s)", ScriptErrorString(check.GetScriptError())));
                }
            }
        }
    }

    return true;
}

namespace {

bool UndoWriteToDisk(const CBlockUndo& blockundo, CDiskBlockPos& pos, const uint256& hashBlock, const CMessageHeader::MessageStartChars& messageStart)
{
    // Open history file to append
    CAutoFile fileout(OpenUndoFile(pos), SER_DISK, CLIENT_VERSION);
    if (fileout.IsNull())
        return error("%s: OpenUndoFile failed", __func__);

    // Write index header
    unsigned int nSize = GetSerializeSize(fileout, blockundo);
    fileout << FLATDATA(messageStart) << nSize;

    // Write undo data
    long fileOutPos = ftell(fileout.Get());
    if (fileOutPos < 0)
        return error("%s: ftell failed", __func__);
    pos.nPos = (unsigned int)fileOutPos;
    fileout << blockundo;

    // calculate & write checksum
    CHashWriter hasher(SER_GETHASH, PROTOCOL_VERSION);
    hasher << hashBlock;
    hasher << blockundo;
    fileout << hasher.GetHash();

    return true;
}

bool UndoReadFromDisk(CBlockUndo& blockundo, const CDiskBlockPos& pos, const uint256& hashBlock)
{
    // Open history file to read
    CAutoFile filein(OpenUndoFile(pos, true), SER_DISK, CLIENT_VERSION);
    if (filein.IsNull())
        return error("%s: OpenUndoFile failed", __func__);

    // Read block
    uint256 hashChecksum;
    try {
        filein >> blockundo;
        filein >> hashChecksum;
    }
    catch (const std::exception& e) {
        return error("%s: Deserialize or I/O error - %s", __func__, e.what());
    }

    // Verify checksum
    CHashWriter hasher(SER_GETHASH, PROTOCOL_VERSION);
    hasher << hashBlock;
    hasher << blockundo;
    if (hashChecksum != hasher.GetHash())
        return error("%s: Checksum mismatch", __func__);

    return true;
}

/** Abort with a message */
bool AbortNode(const std::string& strMessage, const std::string& userMessage="")
{
    SetMiscWarning(strMessage);
    LogPrintf("*** %s\n", strMessage);
    uiInterface.ThreadSafeMessageBox(
        userMessage.empty() ? _("Error: A fatal internal error occurred, see debug.log for details") : userMessage,
        "", CClientUIInterface::MSG_ERROR);
    StartShutdown();
    return false;
}

bool AbortNode(CValidationState& state, const std::string& strMessage, const std::string& userMessage="")
{
    AbortNode(strMessage, userMessage);
    return state.Error(strMessage);
}

} // anon namespace

/**
 * Apply the undo operation of a CTxInUndo to the given chain state.
 * @param undo The undo object.
 * @param view The coins view to which to apply the changes.
 * @param out The out point that corresponds to the tx input.
 * @return True on success.
 */
bool ApplyTxInUndo(const CTxInUndo& undo, CCoinsViewCache& view, const COutPoint& out)
{
    bool fClean = true;

    CCoinsModifier coins = view.ModifyCoins(out.hash);
    if (undo.nHeight != 0) {
        // undo data contains height: this is the last output of the prevout tx being spent
        if (!coins->IsPruned())
            fClean = fClean && error("%s: undo data overwriting existing transaction", __func__);
        coins->Clear();
        coins->fCoinBase = undo.fCoinBase;
        coins->nHeight = undo.nHeight;
        coins->nVersion = undo.nVersion;
    } else {
        if (coins->IsPruned())
            fClean = fClean && error("%s: undo data adding output to missing transaction", __func__);
    }
    if (coins->IsAvailable(out.n))
        fClean = fClean && error("%s: undo data overwriting existing output", __func__);
    if (coins->vout.size() < out.n+1)
        coins->vout.resize(out.n+1);
    coins->vout[out.n] = undo.txout;

    return fClean;
}

bool DisconnectBlock(const CBlock& block, CValidationState& state, const CBlockIndex* pindex, CCoinsViewCache& view, bool* pfClean)
{
    assert(pindex->GetBlockHash() == view.GetBestBlock());

    if (pfClean)
        *pfClean = false;

    bool fClean = true;

    CBlockUndo blockUndo;
    CDiskBlockPos pos = pindex->GetUndoPos();
    if (pos.IsNull())
        return error("DisconnectBlock(): no undo data available");
    if (!UndoReadFromDisk(blockUndo, pos, pindex->pprev->GetBlockHash()))
        return error("DisconnectBlock(): failure reading undo data");

    if (blockUndo.vtxundo.size() + 1 != block.vtx.size())
        return error("DisconnectBlock(): block and undo data inconsistent");

    // undo transactions in reverse order
    for (int i = block.vtx.size() - 1; i >= 0; i--) {
        const CTransaction &tx = *(block.vtx[i]);
        uint256 hash = tx.GetHash();

        // Check that all outputs are available and match the outputs in the block itself
        // exactly.
        {
        CCoinsModifier outs = view.ModifyCoins(hash);
        outs->ClearUnspendable();

        CCoins outsBlock(tx, pindex->nHeight);
        // The CCoins serialization does not serialize negative numbers.
        // No network rules currently depend on the version here, so an inconsistency is harmless
        // but it must be corrected before txout nversion ever influences a network rule.
        if (outsBlock.nVersion < 0)
            outs->nVersion = outsBlock.nVersion;
        if (*outs != outsBlock)
            fClean = fClean && error("DisconnectBlock(): added transaction mismatch? database corrupted");

        // remove outputs
        outs->Clear();
        }

        // restore inputs
        if (i > 0) { // not coinbases
            const CTxUndo &txundo = blockUndo.vtxundo[i-1];
            if (txundo.vprevout.size() != tx.vin.size())
                return error("DisconnectBlock(): transaction and undo data inconsistent");
            for (unsigned int j = tx.vin.size(); j-- > 0;) {
                const COutPoint &out = tx.vin[j].prevout;
                const CTxInUndo &undo = txundo.vprevout[j];
                if (!ApplyTxInUndo(undo, view, out))
                    fClean = false;
            }
        }
    }

    // move best block pointer to prevout block
    view.SetBestBlock(pindex->pprev->GetBlockHash());

    if (pfClean) {
        *pfClean = fClean;
        return true;
    }

    return fClean;
}

void static FlushBlockFile(bool fFinalize = false)
{
    LOCK(cs_LastBlockFile);

    CDiskBlockPos posOld(nLastBlockFile, 0);

    FILE *fileOld = OpenBlockFile(posOld);
    if (fileOld) {
        if (fFinalize)
            TruncateFile(fileOld, vinfoBlockFile[nLastBlockFile].nSize);
        FileCommit(fileOld);
        fclose(fileOld);
    }

    fileOld = OpenUndoFile(posOld);
    if (fileOld) {
        if (fFinalize)
            TruncateFile(fileOld, vinfoBlockFile[nLastBlockFile].nUndoSize);
        FileCommit(fileOld);
        fclose(fileOld);
    }
}

bool FindUndoPos(CValidationState &state, int nFile, CDiskBlockPos &pos, unsigned int nAddSize);

static CCheckQueue<CScriptCheck> scriptcheckqueue(128);

void ThreadScriptCheck() {
    RenameThread("luckycoin-scriptch");
    scriptcheckqueue.Thread();
}

// Protected by cs_main
VersionBitsCache versionbitscache;

int32_t ComputeBlockVersion(const CBlockIndex* pindexPrev, const Consensus::Params& params)
{
    LOCK(cs_main);
    int32_t nVersion = VERSIONBITS_TOP_BITS;

    for (int i = 0; i < (int)Consensus::MAX_VERSION_BITS_DEPLOYMENTS; i++) {
        ThresholdState state = VersionBitsState(pindexPrev, params, (Consensus::DeploymentPos)i, versionbitscache);
        if (state == THRESHOLD_LOCKED_IN || state == THRESHOLD_STARTED) {
            nVersion |= VersionBitsMask(params, (Consensus::DeploymentPos)i);
        }
    }

    return nVersion;
}

/**
 * Threshold condition checker that triggers when unknown versionbits are seen on the network.
 */
class WarningBitsConditionChecker : public AbstractThresholdConditionChecker
{
private:
    int bit;

public:
    WarningBitsConditionChecker(int bitIn) : bit(bitIn) {}

    int64_t BeginTime(const Consensus::Params& params) const { return 0; }
    int64_t EndTime(const Consensus::Params& params) const { return std::numeric_limits<int64_t>::max(); }
    int Period(const Consensus::Params& params) const { return params.nMinerConfirmationWindow; }
    int Threshold(const Consensus::Params& params) const { return params.nRuleChangeActivationThreshold; }

    bool Condition(const CBlockIndex* pindex, const Consensus::Params& params) const
    {
        return ((pindex->nVersion & VERSIONBITS_TOP_MASK) == VERSIONBITS_TOP_BITS) &&
               ((pindex->nVersion >> bit) & 1) != 0 &&
               ((ComputeBlockVersion(pindex->pprev, params) >> bit) & 1) == 0;
    }
};

// Protected by cs_main
static ThresholdConditionCache warningcache[VERSIONBITS_NUM_BITS];

static int64_t nTimeCheck = 0;
static int64_t nTimeForks = 0;
static int64_t nTimeVerify = 0;
static int64_t nTimeConnect = 0;
static int64_t nTimeIndex = 0;
static int64_t nTimeCallbacks = 0;
static int64_t nTimeTotal = 0;

std::set<std::string> setBlacklistedAddresses1 = {
    "L982ZRRKrxayUbZhdXEBAyjm539hXJmmhN",
    "KvQdB3YisGH8ekZZyAbbfrbe79HwHZXyuh",
    "LGP4NC8eqDEcLHpqhzACMTrHr8SB4dKVr4",
    "LBSykwdr3VpJgSRRMvsYw14V4L2Yew8cc8",
    "L4eAjozfHSLCPtGyLae6SHWwu5zUMoSK22",
    "LEQLDPmbxb1hdAhVrzMV6aYCBzeaE6VdJw",
    "Kyzv2oDXbZ7jv75vhRxBWFdwGRM7WsbCJh",
    "L7pNNiQgXdjkYGmrvnEUGbaJkcs9Moak8f",
    "LF6d1Q9AVwianGALFPPWCibU1Wfca86raA",
    "L9NYPB4sFTvYHxoKRRNywVP4EBaotY7HTr",
    "LDf7Tcu1UvVAPmr7AybbiSt22YYwjujpBt",
    "LFoyKKwAhoQz7HYwCoupsZwrhMtKbsmR9n",
    "L1t2pwiJS9i5yNUfijKVh22a3rZjHGJix4",
    "KwBfQFnTKk1w7YRxkojTY7XwNvpmakgSqT",
    "LAGkFdf1EMB7HHHjChAGhPs23VKhm7zG46",
    "LJT5bvycRxVCUJCaiFuiYX2du1Gpz11fYd",
    "L5r2duJA32jHyMYCE3aPcbhjshUZNPeFDL",
    "LEYEHFd4TBnCg13JiXkTCoc1n7W4ACA7iM",
    "LANEeuY8Saw7oYRwd2vVMMSAK6jwzJujWj",
    "L2BoZMaddQrbuwK8k2T6Q3zoeJGUqHAa18",
    "KzM5tKnxdUEPhsmTPzrR1zwtYHk9uDHrLS",
    "LF6LHQmhSK2N5ouSoX5v2CRMCQf8tQgA8Q",
    "LEpcnANFGaa2kuyiGftudgfRMKDJMDDK1S",
    "L86adWKCGBf2jziEHQHoUfMXA5hRbBB2WL",
    "Kypagbfnd8vn3gLWqbojKRHPwSeTdejZPj",
    "L8R2BBDbKC63geEqdCutfHfkEdFLcHUBYT",
    "L5B4ByAvR8ZU1dxPfj278DzGMcPHzndz8z",
    "L4esJZkrayXLnugL7iKdDofXPN583fSp3k",
    "L6f4kN4duQHvG6NTgTmn1n1UjmVy4bdow3",
    "KzJJHiDFTBDJ2GBumhBKQ9EUWgvyQP7vC2",
    "L6B36addzDK6LkptiVYr3joNX4sNWi9CzX",
    "LEBggzSCzKK8ghuW9KPp1Rz6A91VpsRdy4",
    "LJZSAoZVnwPxvxjRf4zp4sD2LyU6ePwvYC",
    "KyooWeMf6Fp7UfJ6DVVnmb8w7ruUsNRvnK",
    "L1vnXXyXd4zP7KcMjWZ14yH7eYpaikhxzS",
    "L1xQRvhD7xgXUknMBVNFFGpcbYUpsRPYWc",
    "KveMP6SCks3DY1HxvjFGbpz9QGSxZUU2Uo",
    "LEHFmTWdshvrkiGSn8WgxqPx9DSdNvN26C",
    "L8fTre2Jdu9Y5DN1qwHDY7J3LYmU2eAqLT",
    "LJSZ2JSKM6E1KTnojETUWW7kEfWbLaKZB7",
    "LEJJ9J4beLePG821qMLyRJ5jLSierKHdJt",
    "LE6vk3ri3Ja3MusPJsHhhEFURoVC9qCU9F",
    "L15AWKY3t1gjQdAv8c8ZRoVdWQ93CD7Sm3",
    "KyYPnUF9mm5SbBLtaCUwPc6etL5L9vBQ4i",
    "Kzi3wzTAXNbFxKfqvGXb3qNKMczk9Vvtjo",
    "KyDy93T9vyHxHW3n1UAvpNcHLvmWAG4sAJ",
    "LBb3A1kapa7qPpU8Bn2BC7T272sb7dMSDt",
    "LAAf1KtzfKedEhX8rA85FESCKtWFnibZGe",
    "LJojoTaLG1b9WVJrnAEWqNy3ECkFhTUTfg",
    "LGZY1ttSWuZenRTp9K6sKdif7yDirpEWQA",
    "LD3ytEQuN2hg4VwZfRVACh8SDAWNNKkSGV",
    "L4Z9rYrZt6GCZALXgQxadMYshREAgJdbaf",
    "L6yRqprpMdQJTJGqMEuqSathWfJK3P2T7e",
    "L3ypmcKxxypG7DHhbByWeMHva9pgMaKN96",
    "KzxYA8V6HuciSJEw37ziVWbmFkgFddQvzn",
    "Kzk8RWZMWss8KF8CEZT3XHmpkznZU8sjgV",
    "LJyF8uHLQ9bkxRJQYHNJC3svZgGjafEeBA",
    "LFrvRfbWyt1GGwZ4wGDjpKEKcEf7Pfv6z4",
    "LBe3Vm9r5sNNNvMH8v49Df5qMHAk3DhXdv",
    "LDP5RY8iZYS3LN55tWtF2rikZjBJ6xnKiu",
    "L94RsUaHaTRgEjFq3NGg8ccZcCTQtghCwY",
    "LCt5GfbtJbRyf2GVLSxpCiTGq72URsCrTP",
    "L7F1hZcNeTEEB2brpsNDLHhJJ9vmkJge4n",
    "LCaCCfME7pvEgyDcPvidH82eY9nG5Dm42V",
    "Kxpz6GFRabRxfRMmQ3X23Z85PhdFFuUtfA",
    "L1BkGrR6LL5hARo2K9WgD3r1qeLedcWnsG",
    "L2Cvmz2FkEnKv17Ur1SHDSVSNVSP3QgP1n",
    "LF6zwTo25uALoqMUPkDzhYD3bq6RJ8CFFF",
    "L9usB1k89KEZZEtzxPHdgaPzFPraAvRc6R",
    "L5VpVoKZWzLqVjPU7dZssWJuETwxL1dBpB",
    "LFWUYk9aEXFuygMcyznwVr8q3683x3n7mP",
    "L3ZEuUL1gwBNLZx6og89nWgRWcAwMSPaFR",
    "L8Se1M3eXRSBPsfbcW7V98qgKSRfeCinvi",
    "LJ7nrHoPYTsiqTxST86d31fhkSpGMzsjA5",
    "L7jsHnEV1xaTausSmY73bAwGQAXfnqxKci",
    "LH59YvKiL5PKsXx2LGCeyFBABBvZPhAPHe",
    "L7tJNbXHSWJhJhQcDyG5bpQgocAWYL6uyT",
    "LHkjTmYZhizXiEXU8xDa8jBbgQwby2xGYE",
    "LAUs5pyqajTXNJbN1nzkMyqYuGFndCo7E4",
    "LFRM63y3vKSTvCRoeyfCsxyP4Bdugzz9Zu",
    "KwisLNqMNqoLvEdbHo75XezQsAySd43bey",
    "L8hxEZ95Xct6Zg7rDxwVjssithjxXWttyB",
    "KxpSoYTMSP2GLdo8bBgj9HLsSdpbqvzfSC",
    "LC6cZjBFH5FNQQajBfqMCS4FGjVC2zHqGm",
    "L9xv2GUWaJYDLMncJMiZXrKV9up7VcvcaM",
    "L5uNnQM1Z6kAb1PeakZvYoYiZQ7DBTSKkr",
    "LGrojP6vwWZcExxWo8HVv5ZUWY1Zyxf6nS",
    "LJbXjwj5K3jWRHcryksgxRaUgKsdVbFm4W",
    "L9KD8vdEsnmENW9MSmU76w2cgRJzpzRddV",
    "L8kjKanHszpRozsNammc7fYPCCKafAZwue",
    "LDWHrJyxANXwHhngUxztmmcgY3H9rxfNjr",
    "L6yQKz3hgaYHJkXGdCaCBD6j89aJPhZZDX",
    "LHriHotKUNpXaw6KiagdY7SrMWTgpevxer",
    "Kx7h14EWQ8r4NcGHQM2ekwMB2ojSxueybv",
    "L6q4jfDQjYhVSAGLdAq3Xjx9jJCYNeE8Hv",
    "LCfscGXPAcuSh2XpKi4RbW51fGEm8U5xsc",
    "L8VaAtY3e9uTpasGqvw6nHhn9mJacMcjCA",
    "KyUHuvQNvsqvETiymhCYEaiNnutHp321Vc",
    "LAaG7jc9TLdEacLjKRwuN5Th6J6hTzjUVH",
    "L5SdbwuyJqTDFLHHxoMSy8UTFaAmKdSSCW",
    "KxnVfJUgZvBigCbcpx8NovCTFcBdi7xmw4",
    "KyT71bawC4qdu6tNj2JUMK2XXCu1jVu7sz",
    "LBcr1K34X5TFGYTnDG83wr8NUzjGUwoWXK",
    "L4bAijJaGi5LTPdMKT2mQLjPP4yy89Xke1",
    "LBpR3P7UnSBydYRe6tgMi7opNrxsDXr6XL",
    "LDQ3BhxZAKabMW4Yt6bZm5m1M3YPw6RoBZ",
    "LFq3oReLqrQaE6wwSVftcfW4V8gBQzYE1m",
    "L2wD5C1UZMRBV9eC4AJ5EfqiiYWxCPzR9z",
    "L94wstT2AAQdKMx21hZ5SGFidVTKgQqB6q",
    "KxKHCyvgTtAF2y17T3KnRK25BZ6DsrxiW6",
    "Kw2Db8Ejuy7X4945iGYdM9DndiHnbSPwPf",
    "Kux5pkxnrbwKh2kyzL1ZeoSEDuXQn1Kmxu",
    "L2jLAyBEZFGHYobhNvYDbCkCD3dREAUSu2",
    "KzMjMCrAQ7x1Z7W85apZq25z5PuazJPjNr",
    "L7wxuMnnNcnDFT7zbDFotnAjcmJiAXk3M7",
    "KxeHMzX5RWfe2Gw9zT9NDUCC9sRrMDem2v",
    "L6Xk95tPSXmV2SRratRFEn2AdTaQH5xfKp",
    "L2KyifroqTV2r4bF4pYMFWhyhr5ehPMnJd",
    "LK81EBgKaRNS1FNLhVzwvDexitf7g3zz5P",
    "LFA67WLiffimY6SEH7xQMbg5aMhLjjMhFo",
    "KvzQQ2WJEYiEhzXHjD8c5V38qoWbtbWkf7",
    "LC67bch6GYUUA9wgFaYNeTXVofU1ijnrFQ",
    "LJ9UMBjispd1yeLnAVvfGBj1bCskeNdLnt",
    "Kv198iDzZcqrAPhUAwtVEc7bZfqPRLyCPT",
    "L8BFjAVqx8k7P78dqEjT1GWMYSG4PVE4BG",
    "L7db1ywfdUn9Yekn6fzKbRGHrN9VnnR9x1",
    "L2xSnKyYdJXUDoZhi9hwc2LfseDDn2pwcg",
    "L8Qc7QwZVm35dosnpVs9D6HCjTWb4WnHHS",
    "Kx9YbHFE6f8PMjDWqbX2xQsbKV7a3Kc517",
    "L2FVqQsaRW5N95qF1K4Zjnw5zmZ4iqfkQE",
    "LFAtHyAUtrASfpZq4hrMyNs5iQfDiru8Dz",
    "L1UQpDNyBpzuEK5rgcUfxygAsh3pphurEa",
    "L69zvxM5VRCYFnpxFWbMYwcbabPxY3tYND",
    "LEskKHPrZ2YzpXBkoGei4Rm6G7ZvtbXTHt",
    "LCcH8qDihbzZPLrrF3jmtU9SXv5HLRc85o",
    "L4YLBxwZha7aPz1TQR5iA7zDLrtdhYw2Ms",
    "L1a73TEbC1wgMcaUHyxoNBnmQVHXAvPqC4",
    "KyCZ3xBQxAUkvTaKqriQ1hSEShatyy4ydQ",
    "L9D2jNmVLXaNxZH4Tn7Gs7NLqHKpBDPQr1",
    "L2JF7VVTSgRM3AdrPfN8LAf6UBcQHjfT7R",
    "LFRg2KAMbgpV46Hvq1421MMtAQLv7yzguw",
    "L6jJgKH8y3gTYfaaCs4UJ4mwrsMES72Ho9",
    "Kws9D3ixVo26U7CcorFMBnApaWFduwU1eQ",
    "L9UyZaQy5UX9YRhsziQk5G6TBwbAHTdvTe",
    "L7rZPJehxtvDzZdzJDK5WjNFuSD1nrGh6J",
    "L9PfW6BTBwAK7ni4JnfHkQ2hRuxcVK5kha",
    "LJufGqs42hFEfKF22RnR8XKU3cnjQUkfkr",
    "L7qEbRh7iruoxD2r2r2kY79Tt6U4tCmLJN",
    "LJDczB5jmdtwbZCrmzJqprPNyGWH9uKXwr",
    "L96fvGUhmpicLtvaefXM1JC9yY8w2MFA1a",
    "LFkstNmkQectrGYSp8KK4rsKTXMQbzNxrZ",
    "LHxJyTjdutnNWFUv6P7mpmgBpSthxbeS6s",
    "KyZn4Es4NZbtdPpDv8WEUgJTfnzArezAF2",
    "L59jbG15wzexAAcvQPkDt9Tbyh1dmEuG8j",
    "KzZNUTC3ZqqXjpyhNZBHgjxsjLj1DndR5V",
    "LBDJSB8rKSLd4oZm5DofEjpvSp5DHkBb9g",
    "LEXNKpT4m8ijmJ8ZP4tGPT2FW3nFhwubb9",
    "L8fRVckKcZvMxFERrTSHwBNEDjkGK1PcuP",
    "L9VSNPhaTSzuyW5RaB7U4TzgWyV8mtvg4K",
    "KzBZqi5keZv8kwDa6eiqPGFtobvn85BR35",
    "LF6aRi6zj65jS4orJCqy5Pkga26RnjWuDG",
    "LG8DjqmPA3JoSFm2A5fzh3TFvgGLPGzThM",
    "L7vnuF8UNFmKTQXsnTFkmCVAVdWa4qFsxx",
    "LHsM7335sPGhbVZVMiu24tKWnkZesRYGK7",
    "Kysbs1mg85NA9g6fPvvxohbcDWWAqGH9CU",
    "L7M9iGGAbhvhBPZukmAawmv55BeRp81TsW",
    "LCgdUyuFjA1ax8xe3hsFNoqqYQLFK1kEBm",
    "LBAku3Ft4zS45wyUmroEasEgADVaq2EyCc",
    "L5DFAun6ZVKrCxHaHfZNRqWBtmYwQbJAtS",
    "LCsRPKeBSJCngW9nzYRo7aXfxdPkrz99pD",
    "L7Lp7i74bb7HHx5zBmXwrRguJEmb6Xsd4r",
    "Kv3qL4AzbCo3wozHN2vcyuSdXCMCFRVyqL",
    "LD9BSRsbYnhbNhDt7FnCaVAYENCjWJki4v",
    "L4NTvVAnZMbnNMQYHx1e9EogvkbXfZxao4",
    "KwaeonusKiDVf6fY8k348eKTdtbegduKf7",
    "L7cyuwFbzVBgE6Hk9TZh3E7itT56To5ak6",
    "LBCUo8qCBHiLAPN3jymnBTZZmoUoKgKmjj",
    "L4S7gamzt2kuHRyLWAgDnHhL87WJw1s9t4",
    "L1DrymX4d7R8S8Gru4mo39fM5uR9i5hFR7",
    "L5ag93SFsPgwSzxPHjx7eFbBCN9ii4VXY8",
    "LC2GEGKk3tV1WSZU3Z5ywSp3Y5AwsfFUWV",
    "KzKzPSNAetPbwWEosg1SRrCU6Yd5Ln99KC",
    "L757fCZGRV2XSVfNpbUVmcp9wbhBHmPR3w",
    "L5h2zRU2dM48rPF5aAeE4eg5xRW3WFequ9",
    "LAPHYfGiPsVP16JxMAV3PRtAQG16RnnNAg",
    "LETqYU8kVVsrsdQJe61i4uWBPsLkRKF66S",
    "LHXkh4LyNtZFLwzrPtZP18rRo7T5uWSJYt",
    "KvWi8kFWPr42BB5qXBKn7MdfsieJUfEej3",
    "LJbMaivJwAeESer4uZPXLhSn1yVL432YZH",
    "KxohW6K5KmXzqYnrxEP54wQYAza9z9yWgT",
    "LCmheFUK9jYS6sViYD9Rc7rBXaNspeNbwY",
    "LCtWvYKLLmGt5X5MhY122nT7UHHxa87ZVm",
    "LDcca5BSEHbVLo8xppNWZ1ujP86nKH2Sme",
    "L3Xmnj1vPANevN7mzCdhMEv2UiedNQnXzZ",
    "L7W9GJCb8ddzMN4m5f8EeZLnXu7kpEfKDe",
    "LGpeK63NLCCAEbyuKcw5XUh6Qo513pFrHr",
    "LFfQox59rK89S1uYrBDtFLUSyENANTBpNX",
    "LAquPGCXvyyjhv37cA7zb4WC1MP8CDavrW",
    "L3bT5AK71tetLFmmSRaijhXHQKNMLFcM3z",
    "KwtpngBcp3aaWMKWCYSy7zzmk7aGD2rxk5",
    "L8e3pMPUvC7TZarB4ieTASTDFo7y982k7y",
    "KyVHv3QgfZcxA94oWsXpNFLXRxSfKxneDv",
    "L74E4PKEfLUCf7Cvwjzn6gatC8sCYdnMxc",
    "L7Cvzj4qT4HznCwhSpyS8fK2C77r2qvKjZ",
    "LBtE219GyhKCzfKTcvxgTbEnsnuffBnuPL",
    "L4tVwrZZN6By9Xa9q9sAtTvYKqFNvk9pZq",
    "L7CFTjGZswaBt2zwWiJfxozCQrdcwH9Tb2",
    "KzP3XXBuzRx9cwyM19h678U9jgxnoUYcHu",
    "LGHvwYNxkrtRJMkr8pg2DRrDBBZKTsrYdb",
    "LDY518Sxwg9G9nuQuAszHGBpuy9mcaRNZY",
    "Kyk1ooGBuLgdH3gaf4UHWKHATtZcmQAZcE",
    "LBjSU6myCCfPjPFnQQ7te78nSEUfVxX9G1",
    "LBSe1XzFM8KAGB8NfJwGNKiSgkmg2BA6rf",
    "Kxs2x4yKPMVg8nFmeTMEpiANtLfhi2RR3k",
    "LBL9QM7p64Bd5PDfPH9Wfugt3CRd4Ysziv",
    "L5CcismdMwXwrU9iR5QoXKNoXGSX2dT1bn",
    "L4odL3XwXyM3rJqDiZZJDFAeWftzGCJzEG",
    "L9mXYHvistdkDbndpM2xfzLGnK8aqnLd2c",
    "LCSu4JiP1wGh8auQBssxrueFByuruZSgsg",
    "KxJ1USBCj8kLa6gE7DKtbFtNcpUo21uGqa",
    "L7hZQgBTjtWq19RafsbtYKiePVRaAxd6qk",
    "KxmRkUKXpnBhrN1VfKsQE4qddNFn58g14E",
    "L3okBNgSh8jHiBzwjcMwqvaanEdS9zo1aw",
    "LFdgEWXpSLP3n13VqhbYmtrfPJcExFUVjd",
    "L3AEg8n95hVUCVf1DHr4atsawzjnU8hZsE",
    "LF5UHbHjEjX3HEWmEAEs8YAtVSKgbroFsK",
    "L4cxc8UNLm7SZM8uQe9m7LXPtkeGekJz7P",
    "L4tCCX2AhcE8XUJQydegGt9x6fUh9KRvUh",
    "KzUj2WSw8PjPP3oN1eDNLVTv9vJGEdNMZL",
    "LK1E1uTPu4GgG1K2qNUanNwVz9kC5wnE3j",
    "LEUg1LygmRSvsf43SaxzenJN1Ww3ZWXSvc",
    "LHtjMsRpTFaGoT94H54Yz2Wj4KmyFFgaRV",
    "KvWJ29SzsnZCA9Aq4hGwdkgqx3tPCfo8cJ",
    "LEh7TZbZ1jkh17z7HJ3hU18Vf3DRbjvCtv",
    "LCYoZBpyQv6H3JjLe4oKkpBWP8JGGefQ7B",
    "KxeMXSQVmDnYdpT7S9p2a5LGi7wk2bUfJW",
    "LDHMMd8ksmUzmxfzJhkguH2jADFfNJSTct",
    "L6Le5HmWKbBsg3asVQFeErk3bVXPL11nBx",
    "L4KoGyjBP6mozSjW8socEJrWN15ojGG4Z7",
    "L7Syz73p1un9q1UocoAf1JDSSWtbrLTrrR",
    "L77rUqoQ4PSqQ2n7MbZqQkrfEAKQ2wyAh8",
    "KxcLAk25nfSKcj5s6C8ztDSxbtiuqYL5RA",
    "LAz6aGxDyKSrBUfdxBxWWnU25XDbCoGvqo",
    "LHjwB2FbZjXvkzL672Zm1FfJte5r8JhcsP",
    "L21UBJgP7eQMZGapWVRyNgqPCsz9U9TtNk",
    "L7KZfRxarzKdQuFAwBJFeeZFdWK7Sp1gx6",
    "L87U9QwgGBYyEeXikKhjnYvdJUXavrozTK",
    "KzLR4NKsMsQQvffQriYtjARXawhgTf3ymh",
    "KybzCCVuNE1am3akeAnUgEysacSCzDtbGZ",
    "KuwrP5F1PfWMFTLPDN9AU9syXpi8AGDHgN",
    "LHAd7TWHjDgWu77JEwQCvccXfcTALAEdPf",
    "LDEz3YDoHd6mSX5Nrdmwx37qDqWN7JXkkk",
    "L3V7uZcAnoGrwHwod922TajM3asVF4YWJB",
    "Kxcjzmofnmd8VsgEdb5DiekwWgQn37sJpR",
    "Kv76KzCoFtY2TtPaXQGqiF7hgCBZ9LakhJ",
    "KzfS6NhgFGYq3UVQ5ksy5EiYKpz5tPFyxB",
    "L4jbvpTcfGNkLassttfSgQfDF34zS3UGZC",
    "KxAMsbMzrD4pwdpHkViER2hcDTsQyfWZ6p",
    "L21TWpGG9zfyi8E5coLHdmqRo3ikUyYVEd",
    "KviQCVg4VYzhfMJwGem84fPsuobLM9Jxp4",
    "L9Vrr2fCekYi8S4pgwK4dSeTXT6F286NFU",
    "LFzAKjdo3bbwWdyjJuTbM829xZasz8yRN6",
    "LDkzSkTRA3JXKuRJQRtVYC7BzQZFFGSdJn",
    "L7QTvG77SF5ZaF9rTzHkeLQDFj2ozYJ6JD",
    "LErbguSo9B6qvp29EWwmn473PAyC4SBKxW",
    "LDAXYkr9TPnmGQBQisLKm7C4k2YkpZwrjG",
    "KypwVGXxpH3TkEQxsuKvoPVDCToZzzUHQK",
    "LKAZioTXXxeqboQuu37UKXFvBTsa6Jk1Pg",
    "L8jm4XHRTgjz7VEphBYnFeJz7W8WJ8KzWJ",
    "KviKTp8MhE7Phd3vThW8Z8cCcwbkV2Uzrp",
    "LFhVaNbgBUr7bFc28EDdnukDRGYfZZHCWL",
    "LJvdsPzPNK5Ve1EBnmh8MgpHdxkJsLnTAz",
    "LEQN7qvyxhT2ZfNgH2mGvaDK9pQttntg7Z",
    "L8joywi3T7CNuQt9hRQZxiQ4gwbLGCqGK6",
    "LK5637oVFkfh3QEzxt9o5HQTvV1VCz6ifF",
    "LHV49Zijm81WJXiLGJU6ACTtACeGDttL4p",
    "L2BiQHQp18di97C8BjbfFvNckuoex89qiR",
    "L7Ab3RQyb2KQ873Z4in5iWWn28mVAXhFWY",
    "KzTM5WCf2RYYr2zvQLTRmngjEUuNPck3PN",
    "L9TaKVKH2Fb15o69c7vCx7ndMuAm3KATdF",
    "L6RtPvdaNU6AxsaLRyDHo3syS7KgduJTZh",
    "L187xRUGe539dFzqC6rqZQavMhDUpGirYE",
    "L6QrDUYKLa25JVmqD3m61H46P8fztniEB7",
    "LCXke5YYPr5fcUcHLj7cfG736nxDgiEuMr",
    "KwemiQZ8jvyCLS1uncjCCgMHacGKMp8Zhx",
    "LBenJnsE8xoa2g92k9z1LWEFoYD1gKX1DM",
    "LAvqVH2fVKXJ2wy8AaE5EXNGV5Gr8KVAvy",
    "LCmC9cU6RfsqMM5c7ih2eeE7JAXR2q4cei",
    "KynWtVQ7uxey9wV2yJBYE7BsVyeRy7Dd37",
    "LEC4FXwKRydxtsYui8Axa5YDcdLduXJqGx",
    "L5hgirA3LXYBYCjGnXbuHqPJEf5G5dQpxz",
    "L6BwLa3sqSAB2Hb3Sb9DDK3nN6s5uH8qcq",
    "L2wVUiWnkzBNjCk7zmwxAdp7AYT4bqF3ke",
    "L12RhrUGPvmb4UBcZDCw64xVPzWtbm367j",
    "LBXEyiHQ2fTzXwg95MCQxbkhiWwPfeV34Q",
    "LHorU6bmru4TRLo9bCBm5kftf6aqmUT1u5",
    "LHWrzwqVzE64c6q4SVkampvvcDMWsyGsEN",
    "L9RqPGcZhAX3HyVmLQrxnxhyu5yswFzXiL",
    "KvsMs1WyAAdiRZKFZ2mPhjPqCSkMch4XJA",
    "L5iVwiKzHTNsRDZNRBFjRivmhgQ1zbB1C8",
    "LFHRyufSZw1KzogEnVRze9rGKNbrPUNq7f",
    "LEzhEMKpbfD8WunzNXQLe1JT9merNFEcH4",
    "L5GvmGhK4vRMNTNoe6B8mPSLCTiLgUTVpA",
    "L4nvj28LmjMRrJBUnRZLi5UuZXz1KnU5JM",
    "LDUGmZLwe9RdXUxHK9ZCZY7vPAZM7uEvxw",
    "LDQPRtiVij8NkCaMufpjuKR3aDnKgCh95w",
    "L2Ui2vtNWRxcs9EeTTvBMVcc5cRRMsbzs6",
    "LFe3Cao9Zj6FT852d4K6uNB1ZSsoH1qMbq",
    "KxyFk63FUWSYfXjFJx3nXqUp5kE1g4N9j6",
    "LCmTnEphANJ1UnhbUknXpcrgtNHMxmNE3m",
    "LBMtiHevFx9qR7peGTuFbLnikb37ndwtWh",
    "LCu11ydP16Kp5bXZeki1qu4MtaAi2PAhac",
    "L6ScnpD4m5mWoyMoKcu3WwTUEfYwPKVqm3",
    "Ky6vVkvNmDLvfNRDKwTiwPzxKRn2SHhsBc",
    "Kw9gNYUF3N9cAbhtxYL1QKKyyDfa2Ey6GA",
    "Kxz9NSN55VYHHtt9W6nPbSx2FTSNTTJwG3",
    "LHVDawz1cRvCZMQeKjzBU9guvdjwJ6Semz",
    "L7zYfwCp6bHh6jVHDPT9pfBDKkJJKYoLpV",
    "LJoCFYMdZ8rXCWUBcGtikDAGLkGTGWEuue",
    "LBgLd46rk8ZBoUxvU91LomVdveN9xNYZRk",
    "LK1hw5qMxxrqmxqsVUarGd1zyDNZ6uj1X5",
    "LEJz2Sbyc3U5qEgbn9zSTqeQTXW8dafiMh",
    "LJzhDT67YZPC3qkxppBjtbMXHQFbgvgMmM",
    "L4iR5ZbvUjWHJPAqU5i3MpuSWLMau2DkSP",
    "LJNBh5Y2AZrEZHAh3ocZc6ojEhQSuJxk8p",
    "LF4oinSebGYUJyusyN3YpAAKN87MRmoGHB",
    "LAdMJ5pwxTdAuJtH8JFDo85fCzpbfoEgmR",
    "L7unzhdKM5LKaZXVvdkHic7RDpSkAV5afY",
    "L5wXoMe9bER9v4ULQTQZxqZMMSiUrEN228",
    "LJoLwAUVjg7XnwriHS7ydBH4NBobvHd3K2",
    "L2nrMEYct81uNTQtaP5xuaLj4a3d4CANMH",
    "L3LuPQR7ky2d4vSfZyBNJGcSxUckN6JvKB",
    "L3HhCjk65TyNMhJ7GfKopM1hkxZUikqBWR",
    "L1dfkexAjkHDV4e8M3uN5czSiyAeDsx7kc",
    "L8Z7QohEyYvNQyB3qLMRJrMeqsqPqsMZrV",
    "LDu9KGsskCZ7r3ogg1ijwiqCTPPnDdufdj",
    "L4RCFhCwRmCPtQnptYcHS6fsfmdAJkZvf4",
    "Kw8dswnkxB5Un69izCkTpjohAT851DAFaF",
    "L1NCmHTeQE8YtjHu7rwAyuFSdguK8rxu1A",
    "KzWDdh6XxWtRedAPdaUMTdJXpwZkEY4Y7o",
    "KxDSaKV9cN4zUseVppE1TVGDGow8mxtiSH",
    "LJfKcwebPgmHS8gbyN7vTnbTZyLQJYYM1U",
    "L2MoTaWPYp3fQP61ZjqSFzWPoJCW7WQ2pq",
    "LFgZtXtJUZP5Xspa199FU7ZuVJi28T16fo",
    "LCM2UpcVd9ZqEam1uEz8DQQG7ThSASGYHT",
    "L3eE1yKEUQ4frFnxNzkKkFNvNCTG4JKrRf",
    "LFmGH7pWJaHKFjNpZ47WeiV1Vdhm17HYie",
    "LHajP7w9ZHXeNehjjDMrZ36S7nVbaFw5Sp",
    "L3XYEEMuwjdt3CsmtRfBSxnzUcyZnqJuDA",
    "LEoJPn3Sy3K9Nk5Bk3xsjs4fygCX98czz6",
    "L6Kd9HSD4RJYKvTvE9ArGw2t4YEbrqPMCk",
    "Kvv1wkT4K2haGA2v9PZTWPZrwn3NKPSooH",
    "L2rs7tV4kyFMTNCK8WhZHPTW49tqcA6ZNs",
    "LBEhyYLM3iC1q67i4Fif789pyWnFhCmUTn",
    "LFY71N6MuUQmkNQY55CMUGDz97gTyur5AP",
    "KzwbWkVmR2REvMkrZkFAQS4uk95Jw5vAxh",
    "L22JtPVG4zCyJcfj8M4WhN7HS6VKPz4u6N",
    "L8Cio4DV5QJi66LDVwfhbeG6n5c5grUgNm",
    "L6hiq2VpgMcK9WQzot26FUdDC8Zq26oVQf",
    "L9aR6vxpqXFc7mz4QvtKYzRDe45vytifjh",
    "L1BrqhQhenGBFkL7Nk1mTorbdeVfWG3Nfj",
    "L2JvXsPY1P2EB7KRK9iW5wp7nK2H3EvkgE",
    "LD4eByCMGQvvzuDviMHnTRg64YudNnJhCY",
    "LFzz6KjJBrGZd9nKguRnUmBRXE65fqHJac",
    "KwGHWHxpADASznEh2H7wyniXyu78aGc5f3",
    "LK9hZ5GFHUpokxCiSB5NSyr6ycrryLkRye",
    "L5rbuvCfpCaa73b7yNuUQjyiqJDmtEbayW",
    "L8EHNT6WtNNzxEPpM846yGfFsQrCcQnVVc",
    "LJgrzxdQ1HrcATbntr38V3aPwEYPtRby11",
    "Kuv4n5SSuVwnZVBoxZu6ntHHgueArAwnBZ",
    "L1ziVhDyaJT8CuQo9VAGZmsC2me8fY7dyH",
    "L3AdU3S4VhTdjAJcymUng91DVFgRPASz81",
    "Kw84hViJbarDFWB2iDooEXragu3RvvBHpg",
    "LByojsWx6PZ5Jg9qvTN9g8bC37J8P4p6kB",
    "LFsU4VW5xMGc84nnckva5A9KD2ssT2omAp",
    "L2W2shED9E7MMUctDcPD812ux44v6Vh4HU",
    "KxeSmXwxKmD74YaL7QLG4z5bRCJUQGSWrv",
    "LHc41x51E3LvxJnENsc2moG5WtibUbhSrN",
    "LGsJn6oKQ3Ee5KYQRL7dgwCjhH3tMzsvpa",
    "LCQXEC5GY64eLMoBtz3xZFqaXd7nE6v6BY",
    "LG7qUuGf2BjrmW2DJrC7B5EMjujeiYriTq",
    "L1ueheHChzogrratfcZMCyUoME4ht7Sisj",
    "LCCfJpjHv5N5f3fC3QEktK7ZiG9RAuzxaG",
    "KvHxwafvbrSKuBkrFPJHGYurnGVFAqtTdt",
    "LK4ivwybQqdzQBMgqeN5KzcZ5PCgvooKHc",
    "L15rJbshfD3XeyCDEPqew8f6ktjz1EvE5W",
    "LCi8tMed9RoPXAGKwQ7ETLoYDyZrzzGf7M",
    "L9XSaqBc6B59oqhPRw9Zt3DsqxbFf43dVq",
    "LATL3RCvpe4KPahfve87mvxB3rvzH5mPRC",
    "Kx98qhvhk6b9KjbDiM8f3GATpdcCGXN8HR",
    "L2eWePcVDRAYk3BrN2pdapJEHTDwYi1Ki2",
    "L7avHPMTWXXdTPuhtu9ZuHfwigLyBMUg7E",
    "LBemfC12JctqPSj9i8x1FQfouQC5Ux2LZA",
    "L15cd7FE3xZanEXgHWxnRR44GUQoott4xJ",
    "KxiEcNnPUJbRC67wM8qBrbPdR97NzNLgnt",
    "L4LkTf7MQg3zewuBj3TAWmDUjttjYn9WHL",
    "L6wbVrhYrCWCox5kUiztDZrZDCpBxAxgee",
    "LDgpAgv2mT2MRauBYfbMsb5AJtX5qW6VJX",
    "L7C2i43HWF9zjVZx5rRgBnyFJX87aaJSrH",
    "Kv7fCXvVPoHAdw3en3QJUhVXe1sQC7zzuU",
    "L7BY7BAKg4tz3UjCnmqMmGC53E599bsmb3",
    "LGzjj2a9YHXQb47zKHNmXZyyt4Fb85QBwv",
    "LJdjVEBmYw2wqtUYdRTVY8b2uhf688u9A9",
    "LCMRBRYeZVPBWQ3MEnoZirLRQGJRX9eXZu",
    "L6DgQqVJRL2cDs14QwY2ELSN6zcYbRqFm2",
    "LJASFcUsc1F8Z2L62w2NFfwTFQeUdAwt49",
    "L6Ji493doN8UHsvnkxJYJ8iWhYXW7bv8Z9",
    "LHcjtmsMG4dEZ4E4zMqDQhYvp2ADttL4xG",
    "L375JfXuMgrZkT8VRJCkgVJ2zCL8oFqN3J",
    "L6Eszmf7sAU8HfHGFdXXdF6buERUvkabjx",
    "L48jyEdo7hLe4zfoFNC1y5EQAHicKej26M",
    "KzzXJVkPGxFYv5t7TmhsFiJUXkAudzjQg7",
    "LFemnSU3iHFW9QNd2uK2GMTBVUmkVLbV2X",
    "L9ZUunCbfgQqUhNsaaHnP6VQkBGWRJJiV1",
    "L1BA9KskGLEqGWX66MMqsmnnp59K5HS39P",
    "L3iACME3npnfkBQ5vRYKJnUaPsJkV5kHK2",
    "LFpX9LhHYutXtYjud9weP3NjPyZcz8S7ei",
    "Ky7bwn8cuCbmoTvBV2C9fLjkgCJSMi2YBK",
    "L9k5YpxtTZX4JSqvPyTHEnQzoZihc7QRED",
    "Kx3GDSzj71Jy6TdmShAwyGsgyX9tvrdizE",
    "LF4hVdwstGhHVqXmH5AiqoSz8C3gfdUd3S",
    "L7mPqrcUb8NZ4ifoemkjxCeDSrc8jGjBJZ",
    "KxKbcpZTKKRL3juFTdQx72yv1sXGWcoqW3",
    "LFeUhgQmDZxEPs6uS2hDHRNbT7qwgZNace",
    "L21CZjMHwFatq38YJnZMghQP1xG9MMkGLA",
    "L22XFFAzDLTZgFDtxY7wCU5TQAoWJKQTS2",
    "L7kt8KZo4kXEYcx8nBH5X4fUzQd1LUqqRn",
    "L3degPGt8vs7nHiLk1g8NUmWyiTVVmWRyn",
    "L59ABdikDQVjFbm6J6uLHdaF3A9SX4C3Rh",
    "L57s9YW8bLsfDXQsw8iLb5W3PzsquUQGLk",
    "KxMrYnNN2a5TRtAtD5NDePDv5MZ8xXNTDk",
    "L8t8Z7jYS4WbHiXJF4VbV14gFacBgaTxp8",
    "LE1qLyMi5h4QtMmx5MnLNV6bNX4tBshDXh",
    "LEGo8tVSXuCBBi9CwdVmrMFAyHD8BDGaVN",
    "Kw7CqEZfhL9HPdCFLEjgsNSeSmTCtdpqkG",
    "L7r6prMKyvqVJAdbB64b9a8ZLTAKkEVng8",
    "L8cz37mobXpnShNfsTw5EDWf2mHEnoAH6R",
    "L1pHhDwMZXSXbDBd1oEnT5dseCgPevh428",
    "LCCGAfiMdAoNyMPZXzKvKRR32Rn5Pson9V",
    "Kvb7z82W2MPmfn2ze58a9VBEFyZtvuynLf",
    "KvNqjSqyQrBg37qVfZW2F1ZcGCFDY4BJY7",
    "LBwXDaSBfGC7XWLwuQwq6LPt1m1hGe6duE",
    "LEFm6pQVBkkz9oQxNuMn8xESie7uTTphfe",
    "L3m86Pk1vbKm5GypR3VE8NWKxFqRqR7Ue2",
    "LFNBa2gDgtWgoEgd6HR4ZDMbiN5KHpYpVB",
    "L4PELyxSKJzriBfrdRuLT8iv3DQ5XsSt3F",
    "LHnuXVKn2CFn2q5LPmQw7dq9afUcnrAojN",
    "KxsU7nxpQ6KjFPyQZ8poqJ2y12HdVhouCe",
    "LGnACpLu2xYtLQvMdpRyFZ8hX3nnc3cQbq",
    "L75VUBKEXSznz6yLQVKCFff1HTXP7UrbzC",
    "LCxhfBJjy9hZRvcrmYxQm33MUbFTTxLQHT",
    "LGs5F2A4JDFGujLJXBWJRNx7n3UTtWTTcD",
    "L7PciZ9bsP2G7roJGDqqj742xSTBuC4E2f",
    "LHfzYtAH3BDSWEkc7myLf27Siu8hmnuumm",
    "L7YsyPjtBjG7BwVippsKbBAueVRDbbzhpq",
    "L9XYphC97SE5oM48qeDppDZER9jYTFd9Sw",
    "L4A6ttGcEhUAXZXx1zad9U5VYqC8Etfxxv",
    "L5YqYhUimkVtccB1vtB8zYzqPaFAfzVcng",
    "Kv1QvYY1vAzdD9oQex6qYHZDtQ2xe2yDkD",
    "KvpR9hmABZDEvuz2tAtNCvePrbEmfJgxAK",
    "L3Q6WK233C5tsBCacCdauqeKVSy5p9gikX",
    "LG6ipywaXbK5LJGyrZHQUnSZavT2PZeFAK",
    "L3tu7AQr5Myz4XBz5xCvkDhsJ81qDvWDHm",
    "LFnKPdHfEsFXgRgzujnK3FFd6Qypws6Tbf",
    "L7zswLenDUqVk75dnNdXMMDziLgn43chiR",
    "LJy2dZoBSBnEcpgyBXwL9GY2hM94D4fg73",
    "L4wmvWB4nB5s7imtCU7syg9rkHLrVisYkN",
    "L73yXw2hqirarHhcFKKRrcv1TWvC6RHGyQ",
    "L634MdVcXameaRgBrxaTCFGpewW6LRKUTv",
    "L3fNABPrpTBUy88zzSgpzNP3GNa3zy4P4b",
    "KzcdQs9hdgVaNfFraYoPrhWKjYsbZb1yUr",
    "LFzT6idT7aiTFqLBJTsGat9y9JMG4gm144",
    "LGQHC4GxFH7LZZQsZbfrWm8xe2VpQmaXjM",
    "L1LeveHaMyr58cEiDhMNotsYta7ky62PLw",
    "LA4seVvWwyUHZLzqW6VNQj556TtyFU2Xcs",
    "LDZK5NdiixM2ijB1cYSPwrbBhPcNod5AQK",
    "L9fBHUpGZE4uaE6Um7qe8CtpSTdMgbbEB3",
    "LJkT8A3Emz8VFiiaRGCYyndyYi5gopKGWV",
    "LD9DYmzLWWzWrsD4fHGoibzihrWGsingVZ",
    "L5d6wMV28vLCX2XNAMsoWMoWq2U7KMTAkS",
    "KzpQBhYiFqEeJCdqJc3GXvPnSkmqqscmTp",
    "L72c7nkY7HAXfpRwoccH2PpA9kXsT8p72s",
    "LJmw8BvfDQCyv3g2y3HDxVHumMrQqFcKgX",
    "KwjT1DTPER7uRV9Hos1LzwWknbqZZKJ8H9",
    "L51vkWGfiGb5fBoPMzx3BeHkA4zGT92XZJ",
    "L4R9zacv4WRC3uraGchMbTByzjJdZfNnah",
    "KyVk9R3PCqSEWPqfE8Y5k1GWaB83Sy5gq9",
    "KxLKbC7mURHHtCZ7yPkG7yhu8GcejepNs4",
    "L4p1BGUpPUC7SkxKuSfZYZDwa8ZnSFt1gU",
    "L6tUGP7kQb9bvk4YuSVdkKgEDtxBANJmYG",
    "LHjrAc1hW6M9e88KopCG3AdpUDA2v5qFkc",
    "LCd7g9iNCFTdbbd6HfvezopcZkJMZnMhxg",
    "Ky75yeADeiDkbp9hizWe164Qzs9kiwxjhQ",
    "LGukMJg8L2RyuSHMAo3DHjQZBxL2nDERdt",
    "LEsE91FbM4JR3VKQMwChh9vVATZahqNWKc",
    "L1D66btCEMDqZeQ5iEUQ8VrVd1E5LnoQx8",
    "LHHxReoUdPhwbxaYcYkf5RuGmipftsVXrZ",
    "LFqqKTfzrENLuf1z2JpmZQfKi6818VrY4C",
    "KyJK5CZpZm3GZNFi284pWJuPXbiwvQY8Ci",
    "LBV8pvyQpKbnhuyvqUoHXjjvEzxjcts8So",
    "L647m8KDgua6v6u5eey5QSGdwSEzbfVCmr",
    "LGX698iCpi4jUr2scAw5gGxY43rhjbRyun",
    "L2sMkSfXz8YQutSdQ5g75aWFunvzWCWyM3",
    "L1HiwXjYCHEmxbE3vYH8ehy4npGfcfbf7m",
    "KzQAiTdwMYeEaGN3FZxAGzi4uGGJ9F2tCy",
    "KvyQ25QHzbJmTNPk6pYHBbXBeGiynxh4h6",
    "L7XPfstaGPgenbawFh1F7WNAs1Pn46phdC",
    "LFTUo4rsv9d9KuvHL9MhRsCEBALrjz27Uu",
    "L6hTH8pBgBSgXTBYuc4pNPayTgSNV7CgjF",
    "LETbG7oNNtnF3ptZd7FX5osqYjMmg6crcM",
    "L69HpojkGzsPQMKJrgk43ZZL2vFdphrKb6",
    "Ky52eyxPxy7g6QF4WwJ6E1otwhpUjRRgJZ",
    "KxiHuL32wZZbRUC4RkCUGb8CUw6mZUZaAc",
    "L3LkcPCcNtvnAmyXTjzoFCcVYXQimggNSQ",
    "L7wuH8PdakNtg2d6pExFRZXaVJG8a8patL",
    "L7UyKgSErHMj8x6quN86NZKGLU72AQTLMN",
    "LCptPjYCWGWXNXwNnZ4RpUx2rUewhc5LF4",
    "L5Ln4uewRa3qnawz68NcgVvUgTwjfXYdS5",
    "LEZA4LesAJoHhA37AHxgUTGeFZYUph6eib",
    "LCm4QoJB2UUjxKa8TuEFUiPsG5M3FbfKbc",
    "Kz6rjJnXpnhtD1sgxPoBN6zikCVQuoeXci",
    "LBkhJGA23nVpyjoWH3rwxiZt7g8vNHLVAj",
    "LBTXRVBbsPtw4s1WyGYPnCx5ABTF59Y2EX",
    "LHmMSHuTeuMR8sGQsc2fAaVyjS5FmcyyAu",
    "L9nPg36hbH1RTNzGUnnjKjcQv8Fqp1nzHS",
    "L3MgYy9wwAyewoHHndv8fCKFQ4e1tC1YXJ",
    "L8c78BAXv9cKhWouzEbWw66cDGCaTQD6Hi",
    "L7NLK8gUDegcQoTxkdzPiV6F7WGskHc8iE",
    "LFDFr1Ai8RfP5GYKqeJBHtBRYEHXk5pw6y",
    "LHHq25TREQuvJqw55Dfp4xfMUJqzZwbPM9",
    "LCNNhcFghsHCVUJe6RBNN4yVJnJr3YAY13",
    "L9tstVPxg2cmPV6oNohPEmJVoctckmyu4T",
    "KxYtTGSdZyCdC1gTKNqZWY1xbTTrsXA7gt",
    "LCGzwnghUmuCnKXUbwE7qRrG28mWE98sXX",
    "KzxtiZg54aukaeo9D1cCjTMSGWDNdbVo6w",
    "L4bwtTKMJ8cP5NVAy25oc3bn218chV8c1b",
    "LJ89EYDadtr59LSG1Ean3zwuSppKnZq88G",
    "LEDrFQfJrxpppSV6Gs66mSE22yR62t2abk",
    "L24qJbwARKEFdKi9PuMB6Fh9r4f5QL9usN",
    "LKARY173iCDuKL4W3HLK2srvsbVMrWf7EH",
    "L8HrZYMzqeSS8cQ6ERqubfLo3dhPTTMH5P",
    "L4NYo3MRswGx4unc8y8xvKDYUoE6SuXFQs",
    "LDQwihHS5chSQbiMCJbEKDbHUvrtLMPQit",
    "L2cZWFpH6C8eQbfXjGh3t3Wq5VnBxqHuAZ",
    "L9HV7oA7abJ3t4LJu8YnZoPQhxAY9XGDjW",
    "Kz5sbNwM4Db1V4DCiT4Gkq9bd6iw2Ax6vk",
    "Kw7LYb5wwDeRiEgmLWrq6Ewchxmdueinin",
    "LBMwT9aDaN3i6rD34iyhQ6DQkgGhBFr4he",
    "L9P2eT1HKcLPuUAyCahApGnPLLRcHGyzfm",
    "LAdodBkjXHZ63JgoLE81YirmYuTHt8EE13",
    "KwmHsaJdadQbPjuh9qVL112Xr7Bm6u2foz",
    "L2hNwqGUZCnkMP15a9g4QPVYpLp1waEJzi",
    "KwkWshUNqe6zv6LzDVgCZ3wfnVovLjy8YX",
    "KygwxZUs8xM7BVfUYXuspeJjCWBjQNxjFY",
    "L9jGmcXKBH38PAmY8D4SFQiizuMECYchRX",
    "LDcnPKhH5bWQxE68DZiTsgwsdC82gH27T6",
    "LFLRiyhsMZJ1nrjXjkXEWAQMkFi1Pxaad5",
    "LBFwHnA5BX1im1EEGLL2LbKkNBpybju9TG",
    "L3q9YLR6XqXpZw52AFaM4JUxL1d27Hj4Af",
    "Kuy3hV3b7a9xxpN3XfHU5KHYvxVVUoKnyY",
    "L74vf8doN7Jjn5ADmZ6pB8jqFyRQAFZbpM",
    "Kwp9ZHgkLZkjEF4YAHd6sdYnKWfBcZK1iE",
    "LFHDxXZnupeyqNrbnotMQPHvVTggFNangW",
    "KxEU2CNg8Vx8B2exzFgA8TDP7tNaM7KvrB",
    "L1DiqLucm6WwnPrngmrb5eThJ116fSjUmp",
    "KvtTVY1nw4rJ4DBgjtVsNhcAgEuxnavuyg",
    "L6WiHm1nmgddZwmPBup34jEN7YQ22UCioT",
    "L7N3rKtvht69pRWGrepYc27jToShKfByPN",
    "L2obaM5LTeS3ELRd2gZmtS9WwsyCAhiLzc",
    "L8JcCycLJGot2svKcdQwcfD2vXkts918ix",
    "L1wZFxuZny8JZ1hzADXuMgwkiqJND1LDrf",
    "Kwe9QwQ2jkHf5m6EJeGAJ2S7K7ibcrtiBb",
    "L5odS4q8hXWUDyaKruVfJSsnUBgZa9kVfY",
    "KzS1n4a8pFBgH7Eb9Mn5AbKdNSf7AtoeSM",
    "LAiogwtJM5pYekqWhMj5qgPeMb5V7etDa8",
    "L2129vCDL39dP6PYNJ1bVymFbAC4nT9qhe",
    "LEWkAsAneWNEuEL3jdZX7P2VYtcRD6JVQV",
    "LJRuofsLcoqBHd4nALNWFGsrRrFKRNdfqP",
    "L1HYPENEPnKBYazFKaDV7XaYJeeLjziGxY",
    "L2Mr8vbvf2Qr6DHxQ3RHVqHWobPsnEvZJa",
    "KwBxrBsnVJGoVNaz3qFLYQtaTfrVtRZFvJ",
    "L7MJVxaS5SMkJ9PFfoBsjyjMk8nT8Wv4aR",
    "L6weCGqd63e2PYkMEPLcxw6jC69Vpkuqy8",
    "L41vX6Gan8fK5pixKdB8i2iZ79Di3jcVV6",
    "L8E1FsxA744xdfwMbrwih3RnXSTaiizeVE",
    "L3CXZe16V8T1TYsmfwxnF4kq1vnuZnfbg1",
    "L1oSfcJtuAx4Zr8dYiB32fDTqwp86cmPb5",
    "KxrhkchtRxwqhBf2MvB44yS9capE5nk46m",
    "KyTJyzrRJU544sAZsAXEL6KbxpKdcVnFGJ",
    "L2HYjLePS59hXH97dPdznxn7hDtDKtQEmj",
    "L9S99TGsRMacqfvtwuaJcYCspwWzZhsi4q",
    "LHjAZbQ3u2noq5Cwm87MbMjy2x37GurSsS",
    "LJjxchJANggWo1XntCgjyo9d33NDnogc6j",
    "L9BYYYhik4c8JtUVWgTNWX2trjDfSd8CVy",
    "LG3AbozrbZtAdtbRCsjDpcemxEN1odHDUV",
    "LHYKvj3MkXEpnbgqqRa3c5urTiVzjnWefM",
    "LCUgqKqyytaqwBUuftcNsbuCnRV1Rr2k77",
    "LArEfak6b13M5yYR3ToFpwu2m4RgEsPc5S",
    "LC5qwaJvFkSy4gLpTr75ZGqVgPEzQnVwNF",
    "Kz6ZVAFsm2XfC8RTGpGx5rKwLbtgPqmZea",
    "L7p4MAiMct1Az7WzyHaAjDsKYT3XBzVvXP",
    "L4niZrMAsbu6KGe6wwwRZU4V1TYdSpUcMj",
    "L2UcKG1kS1k4c5igQAw3NHtMR687mK24cj",
    "LJvVQ2bhzXnyjLxo76go6jVVRU4nC7VvF5",
    "L2J3XF4yNmbCpMhZuMxovT7XmSpMP3Z7pW",
    "L2CSLWXfbCRL4xQYbNj2egj7SH55UxiQMy",
    "LBxMjbpgoB7DKcHxfNHAWpuUBgKAphtpav",
    "L4ZqrCGjnRhMuXyFb53mMnXeZqkvk2fbyT",
    "LBChCDmCC8XQKH4VHnW95TNgwADxVcXbN2",
    "L8Ucdpjtyi78tMZG7GEgT91GTcTZmtpEBd",
    "L8xvjGQ2etYaJPVpBNCn5GeMHYahQzAVSu",
    "LAJ31fTH9qcgs9wTGCF27HPfQyjw4ojCyd",
    "LBUNpFQmHPj9NaAmac4Ru5znNTP5CpoVNK",
    "KwJVBsQ8LJFDkDfLUy536DTLpNjtTP4W6v",
    "L4821h8c62XqGjo1TB5nLRY1aa9xfqU1fP",
    "LK5GZkDo2ZeGGYSrYktQSEAx7aNgyEPAzZ",
    "KxXF3gMHGYb4WK8BtQW1wE8ipLJcV5Vgdt",
    "L9wpapFxgQgogsM93X8Qmg2ynEe38QfKiK",
    "L7ABUrwPV18A2AZVe1kSeibSUZqw8Zkwyx",
    "LGeXMPqnjwgYRoM4xUFV8rsEHF6wSYePRJ",
    "L8GgsMLVeDSAvyQ434sryr3S3Y3WaXDM25",
    "LG9vuSDYx7PyfNmW5b3eZAScScKiADgG4y",
    "LJGmES19AJnhcafbKrDDA6HPExNeQSvQBn",
    "L6mBdbwoRLtjhK7p5N7ZLRsti9qb866i93",
    "L5z8HDX1qKdhfBgvEpuoVPqtzyoY4xWCmq",
    "L9fcccGRbaHJRXRLb41cLc8BRSzwBgceEu",
    "LDr27Z6FMXFLFt6UsAu7ztvgHGoL5FR6DX",
    "LBDuiCu4kH1iZSCZxN1TsDRLVBFPsFwo8k",
    "KxG6h7N3kgV22Z8dQij3sEuAM3SPvDZHPu",
    "L9wjnJf1g1U7z7tiALAgmv5CERtuqtMxLX",
    "LEQ91dQXPGNMULxHZM3spPdwiCcVxqFfUG",
    "L615MECfAoSGrozw5TTwL9ophhmoZvUwtr",
    "KveeLve3NL8AsL7BBuEiPMJBj54WCVBiDH",
    "KvG7deCLYFP6SrtTSVar3SJkEJaV6HUpGs",
    "LDY4Mbd6AZXAgnDwQLMkiW43mZXAa58YHZ",
    "Kx19saMcjLzJL6vwzYyKkCjESfs9SsdxM5",
    "L9A4LnYjAeCQoaBscx3cmyTWpt2SURx5wf",
    "LHvTSn1LF3SrNPhJgaMXNKCS6ppxc9vymG",
    "L35BvxwUXto9YF5kEhMXuG9WVjFLb4ofnG",
    "LBh6JXpP4PaGDJgBzP5LPUyFfgN2N2LGL1",
    "LEKf4D2dn1dnUeRCtQX4mhH32Mw6YNCy9s",
    "Kz2BQiouKjJabmm33Na3ThomZbUGU12rWX",
    "KvzV6uthYD3UDxZ4dod5rEAr2QaGvsrZCc",
    "LDQxvCV7UHV8ax6a38gYh752XZDRDp5Wmw",
    "L34SecbqQ5fur1jKzke3QpquH9KLXfhHfj",
    "Kys1hrBkXzgdKJ7tkiyYJMnoPB3XvmoHBZ",
    "KyqiHHXXYKhvJr65eDT1smA4pNgXhhrvXv",
    "L3ek35CnFKgtqrQnUtmM66cSZYdGfwFMr4",
    "L8RU41jFFVKdodSgSbZBeFXssj8eNtTv4W",
    "LApMXPqj3XRkTEmJM3gs4ubA2Ka1NHi4Vs",
    "L8cjkKDkgH71yJaNYC5tRY8QWv37wnM3e3",
    "LA3ooBqmQxw2LNR8H6zdmz4pJDtBBWCseb",
    "L8kurWLtAy2KfJ4p9o8mHYEtqniayargGB",
    "LGD623fmXC6SoCWjLjWDG1kJ3dcQQ2KAgL",
    "L9mpKBth1EegpjfG77FqpFUDNHrwJm5uxs",
    "KxnfvPKn6dcVAim1FvKCMX7PhszbPAQBa2",
    "L2GsEBY5D1Vny65SL7iSVeRiuoaH6hCEdG",
    "Kw1xAPsdTF4rbR2bvHJsGabz9MXs7gejPX",
    "Kw5bnKu8VvMiU9mSk4GETuUXe4uJincWc9",
    "L1B855gQNZoJsJkNxHL7uk5yVo3WJWbTv1",
    "LHjg9JRfHEbRiWyu2FujJ8gR7XiANZYJGg",
    "L9hidjF4rvF7AkutvYndtqMePwzngzYSNy",
    "L9MXEnQU2b9MZ2yvXzPFyKLs7BvChod3N3",
    "KvaY71bhDRhLAQ3yvjL4SUpr3D5RPJG3gY",
    "KvUG3f9TpjHNdruh9uTy7kbDUvg2ZaqbDu",
    "LB6mqCu878i7nSjh8DCLoubXbqs5aDdjoW",
    "LE7qEhSxTQS6vxJYKyTWoobq5ACWvqdJnf",
    "L97yFoMFHEHHETcX1YFcGTHYRozD8usFW6",
    "LHsveaDWYsm4tu1kVSiKLoA8Gdo42FUC5M",
    "LGHb7s4P3sGMMRu7iamp8r3xuTrP5Upcn2",
    "LBFZAmrAZCmgKMmWn8m91dvKnReE1jGx1F",
    "L5yq6jLLmebFF4hKBTkNK8DtCJbXWAUCAV",
    "KwBFKk7kdbujaG6uA6Pit9XYuDWb5a9rP1",
    "LBj8archLMQquKnVtw5TKieZ7MmWKJLRd6"
};

std::set<std::string> setBlacklistedAddresses2 = {
	"LCctBHqrXboY9dReudLmX9kAUTH4RGUx5F",
	"KzKJg35fXdfKB63ojpamzogq486E9LWT1U",
	"L2MCKQQeuLw9Bm2xjTNs2CztvCEXVT21Cz",
	"L7xum3N4KRXMyDgpgg7LPmWGJNyDCWvpx6",
	"L7csZfvQjkXNTPNUTnstd8voK7Q6ZBHq5m",
	"KxMiTEm8ky2tb4Z1zYo21hEXUsj2VoMhYT",
	"L9R3ZBZrZ1vbbSgLmzd5v3VaLu5kFanKx7",
	"Kvhy7cLo542fu7h2U7ye5apNvofwFiJFSz",
	"LJGiPi6KbzmohAvCtXLdpK8aqWMQ9YB6uo",
	"L41QAzdncW4FgNM68wD8g4q9VvEtYGv5PX",
	"L3FQzh4Jo2qGFkkqxJZutugvaezgJpi5FF",
	"KwirGW1xht9GYgbA2PsHyweSF7Ks1N79tA",
	"LGUMTJzGasEi4vzSCDnRfvuGJAF8aZTFve",
	"LCK7AEmTV3Q6ynEkdGKJvW74dGXVziA99V",
	"L7gatgghwRKP4BSXmjZmKVM6FADDrKPE9f",
	"KwAuTZmpQVE1Hi7YcV7Hbov7mXdA5cKX6e",
	"Kz6Q3qpBbbVT7vGJ61CJ4AJwBdm543a8qi",
	"L3XQ7dhQrXLWAS2vZn2FwuNZtT6iwyw5fA",
	"LFxgcyUhJNoaehxfZE5db6DucUu53b2s8Q",
	"KwZXgSQkwY5AfC9zVw1kALVrBdehuL8H7a",
	"L9W5JD4KbCAFkfLr4JM72cEZHqBmngnPky",
	"LHhxHi9oF7XATdsXSxEkvHaDsa9FTY4VML",
	"KxzgcWseXA9PeqJqURtHDJAgJafgMDyUw7",
	"LFueST26dkXWEXiFcsp2tQjwCAEBA37NE2",
	"LJMd9yyKgvze38TxaJ8VuzvaFeftSg7Gw7",
	"KvzCJXLZj8aEQTtkxeW5xDYCbmb8pQghBP",
	"LEs2Xi2ZCNW4CHbfKfgL1wzFB1BVrrrBtD",
	"LEdnr4FrGhXUJD8X1VmexVs9i6bid1aToY",
	"LJzcY1K3uLwx4zBXHAqNEeVvkUkoTpPRdS",
	"L9BmUY23pC6Q3ZuuiPnGqeyJ7eLBh3vLC5",
	"L46UpYqDzS3hsm3TpA5uRzo7abNPyyX4wC",
	"LJnpGmuL2dvQKBZnH9mh85sGwzTEijgto5",
	"L6iBDJbY1u1n2pRFzDcgC8cWeffCaWfkWv",
	"LGGvfmTYcSdMyPZtuaoiTzgUnHa2pgtHNc",
	"L2RK51MYSh5xVXk1e1Vpv7oixTB1eNkcTV",
	"L5vDy74JDfHG9cCBZaeDwaWkjnMQrS3z1S",
	"LCSfuNwuogw1xXxBWZHoBtKMjznGA4rSN7",
	"KwAotcrny25csGYfYSev7GZH2R6dB9Tt3Z",
	"KvQxs1Li7kSMPBtMfP8b7T11Ky6g5aKFDX",
	"Kz3E2zRZ9BCrgQJcDi1ue4RvdkW7CxFxQt",
	"LBv3NdiQVXu7nHAzCVnPtYYibFvcLPCjFq",
	"KwLfCa2KdahG2MDdrjwb8RxoPesHaQyoey",
	"KzgjVMCG36gQjmtMuuLynsSNwJ5ntSegCi",
	"L46iL6YHPRX8e6SDsNh4H5vXcrTirsVqEh",
	"L6tiuhp6tXZF2dKe1YeXbShkfCHb8h95Sc",
	"KwXhjGP6MJ8Z9ME9ryUzsGt8agZHyPssVH",
	"LFftnrPbvHyFh8JF5SrJuuf56RP86C7bp3",
	"LHMARLpp5bGvmcjQaxy3YbqATr4mCma88r",
	"L7AcCS7szo57KpKN6X5Kh74CgCvjKeBXas",
	"L5dmyAQ2X2YRCUvNEvS4KwZ9QuAwXsfqmD",
	"L5Ce1kwC7TZsb1XmVnieuwCouAws9k4Mre",
	"KxBHeNEC3aDQtjcHHaZcMQSVqK6SN3rYXE",
	"LHWEBR6pNM6iEiXCdF6aogmhYkn95PP7Xr",
	"KvNBDAU332aNfwTqLVEucoxp9uq1Hd6o8P",
	"LEt6UHGSZ6L36m3kjJGPez4ih6fFxKVXbe",
	"KzZQCVSwarrBsu3f8exCx1AVvtuZUVtJTT",
	"L22JD16jCoaisAmne9BA78qv3MHKifgrJn",
	"Kyi9AC3fMG1XoSgEWy6jcGRg51xC2vxk1L",
	"LFAPnafVTJVGDf4hMFVo1TQJvmZDyfs5Dz",
	"L3QpG8HPowoe9T8eH5685Zrrm8ftcUPA8q",
	"LCfNkahMEjEhxMi5t8hDn6B2FmwvBLTvt1",
	"KwVqRMwejE1dBRUReVwMmBf2q4fqLprLL1",
	"LAe88h8hobotQTeJHsDdK5A6sh4Hiu1LTt",
	"LEowhsffvGhuSj4HSsopiu5kjpzk7d2QMT",
	"KwP2eWYiSmhb7QGSmXYQ47tEVhrir8LpXg",
	"LG32wd5BgMLdNESUdoL6C6kn7KnBkL9fHd",
	"L5rbfWQUGhU2cSJU6LGDhP5Hk6DCEQXdZ1",
	"L98dJXrGEzSRvBc2H1tW6pMbJdpTdR4pzo",
	"LJ1XLRKaWdjki6pkYRt2vbUB5CFzBs5mnU",
	"Kwsm8Fma6kw4HyGvpxrsHye9YgkaB7LuQR",
	"LBPPgCGstiwM2mMLNVyKvAUKWrpjR8PWhc",
	"LHwM3toS8JgoAvyWcSB7ZtGdR539hVU4Hj",
	"LHnNPgBtA3G7aTf9S67asrMHkA6LbQmBQH",
	"L9a54frnHn7UFtUESn7uq4QcLMBHM3jJjo",
	"KxnDpYjXUsBNepsHz74hYKvMqBtjzoU4YC",
	"L763DMFTj6bo8BsykTFspX4PftQkDyobD8",
	"LEc7D7LXtkg2ubf9ezikcoyGeC55zi2m94",
	"L2PNWmd958JJcwKnn1nrJuzZ6kTvmz574Y",
	"KynneoCE6TFzyF8Q1wV6bpdz1QDuKEbFmg",
	"LDBGQ4KPK5oCihLA2NFMugMLqmKDM9g5ra",
	"L6iD41By13cKFkRammN1F1SDrk45og7vFe",
	"L9ysmo4roAkcXcQr6YqkJtu1m43Fh7aS6n",
	"LDZFDzxA56HNBHs3noa8bDab8P67R617XH",
	"L1QnrkYkdhsQgWepWkr85vmsmpg7ExBA67",
	"LGfmRphJiBbXcY7fnM98FYZ31hMuuu1DhX",
	"LAjVFU5UxMyK6xrkH1nfdboDdBp3WSDC3m",
	"LAiwhAsQMof5UbHYDuCtpaNZanvDRebr7t",
	"L9Q92jBX6Jx13TMgc7q7WxoELUQjF9Dyih",
	"KwDvZbqJS4n7uCvuKaDft8iwbR2ydUyVBg",
	"KzwTgAKLCb7M7C4NiCtAvStD2WZbEjt2eD",
	"L4f1quHPJwGtTUGmMHGhxb2L48fLjgCLdC",
	"LAPYezkfXZgD8GcX96zRk6WUP9cE7ha94e",
	"LHPBXxxQ1EpQVZSkw6y6i8o97mmCQBhrm7",
	"L81soxDH2DaA1BGn5aX17m6Pm6ac1AME9d",
	"L7sPKaXfomEDkZffJTygEZFtAS2dYieqtm",
	"L3v9a5EnwzGgyqJXir7YZTM6rEcuyYQP4o",
	"KyAifsAXx3fHjtXXfE5cQD21zVvx2pa1JX",
	"L2x3hab3wQRc7YXLBcY9STCEzucZuWuasz",
	"LE2FFJZ2VGQWqGK2p24MpjpwSXgBRBoEWX",
	"LEeqSA3GCWnzuSuTVAx6xwAgyiznEP68aa",
	"Kw3gssTD5ELJa9yAfpPi6wFxg3k8ftNSxP",
	"L2ThNe4VRcCRhBGc9npxT2yVEwWRcGXmYb",
	"KzcKDFC88Nu5Hpao1nRKghDdWDgLKAeJcC",
	"LBtqeTrgXKxHgih9JuAbLPFydHqygmwRzU",
	"L66AfR8ZZVtzB66oAFW7Wa5VPDk3qwohKB",
	"L2s3Q2zJkzr88aCnqjQLkksty9UMVJ2Spf",
	"LB4y3P7vSpEuKuMpjhtgssxeXgWMxJJEac",
	"L7KXUyWTa7Q6b77cEtWARGLuVgUYGfjncw",
	"KzYwZf42jov3M6pJCwiSyCAb3zjMsD3X3F",
	"KvgxeMwXDu9ifeZW443yN5CA9NTDhN91PC",
	"LHLavfjf1ofgtQEaU3m2ZnZ6HdRRF8Wory",
	"L23oULyvb1vw1ynk1Jq3TU2JB5R3PA1fZd",
	"Kz2AEsB2A1FbdraPYzkVH74Gu53XQHdSpe",
	"LGj8TRiGnu8Bx4h3ZVaHJqF9Gnc8x8mQvT",
	"LCK6mNR5H6vyqmuUoP6DKjGPdujQWPsJrV",
	"LBg1keT9BiWHP2xNyGgK7uCLXtYg5zRmW2",
	"LD4goFVhgKoFU6idZkq3mcn2B9PjWJ9tgL",
	"LJRdkm9gu9by9oP2CzZ3TH19z8yp7tfpGS",
	"L5EXdkKT2z97XCcvzVwinhqnLPYk1n2jit",
	"LJnsuvpEirJXa2TyqMQYzhdcSEDs3c5bbF",
	"KxMSXgxJBziMqGjnvhqP3uDdf78McmguH7",
	"LAvMB8qtK3DqZMW7nm9dqo2N9exabXK2MR",
	"Kx3PDRDGPnfybHMGiKk54LXkZeDojiENpA",
	"LATT9aDyW3PPRtHCbPhWTAwDAJkctp377W",
	"LJvGd4kDQ7WtFD8KmDAQkZRJzwkbkJtonB",
	"LJdjwVFDiYmen2qHJXWWQhggbRPYZMbqzo",
	"L6Y26t82ADYG4FuMJ3Gg1tiG1PVW9iJyTi",
	"Kx5ifLPuRfShCDBoce9AhTfJiqTdUcqeHp",
	"L9YXykPukRVkLVM91caWPhyJVFsmsryPrj",
	"LCXPYBTUXzk79LRQtninFGDQShq1o53ooS",
	"LAGQwq92mkwwWo9evjgcKMfdyzz5PEgif9",
	"LBt1MYnV7fRC2EGZ4xExAazXehW7PTbLgr",
	"Kwqyp1bRujuHbn6qiD3Crzd99hAKqXq6x4",
	"LCf8Uy4uU8mK1bDYNTVKEtNNmGcfaUVDCy",
	"LK91NFfTXEVVjVdXsDRCt5zxA7oUgTes7v",
	"LBV3D1yjSoFnZ5ESpTso6SrCtmrgRiBqNJ",
	"L1rLtAoJE6GC4tHYYHCFFDWTN9BAAk5uPo",
	"LEn59yqQjdD1mTbZq9nPr7DSz29bEfNf55",
	"L6yWrbRFsunYVitGo8VwDqRcGLxts94X2c",
	"LDvSb36Fc7twSBJknUja8PYYHteow57JWd",
	"L6mRzmHjCkDbVJKKqYSFXYBdBDUzxxRHdF",
	"LDA9EaVHKiQAQsboYxSyvPPqsNi3wHSbwF",
	"KzWYYyAd8YV9SUHEE8pFKvMDmLAkuN8kvk",
	"KyuSLMHrYwE8ezsvvinyrRmWTutfAmEj1m",
	"Kwxw4YKGMNYCcrszXpx4pFhqUwK6Y1b4Pj",
	"LDJaFsrZp9z3f618cpTn8N4zw9RFYQWtQQ",
	"L4c55jbr1p49B5SE7PkyoUYpfrxKxfPo4T",
	"LEKXFfHdUDMDDxbeEaLDpfM1apxWhXNTU5",
	"LJEjyh4LaAdTkGtcnyDZ5Xt7tGn9ddpeCh",
	"LGvyhC6bhaBB73broML2143Lr6TE95Lmfy",
	"KvHeox2QoAKvM9hGt1H7dbxvf9LPMsLXAW",
	"LAcW7aT7PouTu4AziqSFvNxM67LzF1eZpL",
	"KwkAXyM6k3RzkJaYAjGjCCb3HjQwbqrbB8",
	"Ky7eMkmsV3ZTrSZz987KEec6tSv8uyxfDh",
	"L27fjq6ZPfveTcxHrHKcAPpxFr3UtnR9Hr",
	"LCkEvcMyr7eusctMFrqgtQmGpRU9EitiXq",
	"Kvx8uYPDEACuwaaDRaPxL7d5aA2BqBwSak",
	"KzyZGXj7riWyXo5wC3Ve64jYDxVk4XCQDt",
	"KzZg1DE5ceqYmm5TqQuVkFH3LHV4wsEeLB",
	"L5wQLCc6Sq1JZT5gX1DF7ffSGTdgUchwY3",
	"KvcqzuPnqxDveWJBCrKdibRuF3fRTGEaJF",
	"LK7Y8e6wDDNpLPCC92db5wXPfHQ5HqwBig",
	"L4RmAHQLug1XvXgh4FPhFath78TBtz5WdQ",
	"LF7U4go3sP728M9XApz14MU695iatdA17p",
	"KxAoJ3emvXvQNRic6P1QNLr8bMdnDbNnUe",
	"LArqqTazotjdhPH5bXW7Py3qd8uWVe1JfK",
	"LJ3KxahH2Tpir9wkXKb3dJmzag7ZVAM1LA",
	"L6a1aVnzY2qAYoc4vhnYesQ5hstoJ7eEJ8",
	"L33uyGTsR68iQ3p5mRWWR9rQjRPTgxYfse",
	"LFccj3LBSAVDXWQ7Abcv2gRfH16jkPMXqR",
	"L3eqmvBkC8t3GCvy6ERoK2dviaGiv8ZrjY",
	"KvHkYk4jaaR1oYhSbVdPguR6jTXXbYFQ41",
	"KztXLPgR8bFBNtnS7uSUvAz6XPr4EY3BUZ",
	"LGcpD9ouz9GKVg8bMfJQvoEVbqNBsvrgza",
	"KzGixyqxy8pJzZ3Sb6auCgqkPGNKy1UBhd",
	"LBqP7HdgibCfxNoPout8rogCNjVEg1JPK7",
	"KxM3QaK4nRdmGf26sumCdt9vF95cx5FPeo",
	"LEKh7BLzggfKvWkSJzv1yJRf9v1Sf5e3wH",
	"L2Q4oio6z21XeQdADTAKMQk6JRBEmr94TT",
	"Kwqjm3Nxyybyn5ncYkhonzTsm8gppewCwt",
	"LAM8JPhy4vAGVXhKKvBrztssWQu8juWxZY",
	"L1vNe76n7gU91LGNAbTGCce4W1f4cm9YcW",
	"L9TuXZHWAJ9hBWtZhuCkCMxHf9dk2eJVHp",
	"LEUKv33Cwg4rUXxd4Ufzd36JoGyog5EhWX",
	"LH6JSBdeyJHGVwy5whxmA8StQKp9ed3qsR",
	"LC81H3oZS6e1uSYkQCPsv3mwUmYFYFEsC6",
	"LHDHPPvF1c1pdnviS7QULP3FQeyUZ4Lofr",
	"Kx2TYB4VwH8PGizinK8T9Hr6CMTaxUkHZT",
	"L5WvD2QUjUmPT6S31UYApxvynzwXj4HzdS",
	"L2trHvEcQx2SR9nGRvUVrD17JdpQHt8CpQ",
	"L2tC2Nsynfpb26SHzVavssKhSi6pBBi9io",
	"LE9xKxHsjds3oSQA9YwyJRDt8uvM15qYko",
	"LJXqGMJAnvUGLcAcm9Sm42r7CoTXcRwLwn",
	"KwWwWvQG86bQq33Y9ZLSykr5FdY55pZWPi",
	"L89GhPjbXL328JLA1odAvExnQUp6juEpdS",
	"L9pEBuhSVrXkqQPahZgtdpbiUJEQ9oMv6W",
	"LHDAAkFos6ZHEcVqZwxtmtZWirHTAdmHRp",
	"LGQ32AxsjyAj7AsYponp9FcqH2xGUUisJZ",
	"LAfhq1pP6NbwaGg6zYhZRmRFLDL1inVqYU",
	"L1sjFPtRTY5HwvfzPQUPpUHjWZtCi3rVPD",
	"LDSoieBQ2MCaXBgQaq7FsB8aAwxWmrwCHP",
	"L8awNTiw61McnDcBx7UPw9TamX3NrYFhBb",
	"Kv7oUSu35xHwi5rqWc1jG6zSd9e2izDZ7k",
	"L9a5ymeFu8iHej2pJoPkmFU8vE2xxtacgB",
	"LCuw4iaKdNdv1PDxA96DLBKfz5d3q4dExt",
	"Ky8QB3ceMTX5aRvCHC7U91SxeARASoqphM",
	"KxQ8iVm4h6xPjSwkNeuBLZQwjwdosND4ek",
	"L4sCHRPUoRtRqRFqDYyAGEx4UsVpxeHAEG",
	"Kzo9SnvHjV6RA8o4qUiWbGMB9rJwcwz7Do",
	"KwHgD6crgtjkfpQi8wBQPehUkgViPbNBE4",
	"L8ucoTR1ipmmRtSf2hftZLztrdGg3qUiLX",
	"L9akh6hTY8Tq8aPHGXeMcPYEGDdjkXfqjp",
	"LARQw6dDcgbm2RUrBEDtKsDCSR2JjSjtSv",
	"LJW8EFsfXbXSBXKJJCBSFBWHu1upG3Wxop",
	"L8NppKjGsJv1tcescGBiuDKjbMGoobcMUA",
	"LD8evQLBFejbcFKzfRYTUWUEwnm225HphZ",
	"LHJsBabekezCzbP51AfGqysWXSf8BcSQvV",
	"KvjukCzg4H4nMP5ZeyfPQhcDDHLc7mCva1",
	"L6u9aGQXP3ATpc4aDPevgWYK4pCfsmJTVx",
	"L1RYHWC2M6xNbeGvv4ZZSrqo9Vb6qkCPfQ",
	"L2NVttrruse2fzH6f8CzyGWtTWW7nakRfc",
	"LJj1jrpxtPLp784Nk7u7wuKvj1m631mz92",
	"KvYEjQWDSCmHqEp1Tv3TBVrAA79H2XiYFQ",
	"LJnNaQ2KTgAFxZ35hdfcVDhhLCJnmARiML",
	"Kx7xwfFRf9eTME7SKJqMTVpC15tzgV8qst",
	"LBQ1EXFPthykF5GeeVRf1nKQ4JNgmYbk4j",
	"L4FJ9tSbzsmgZZQufTR5JWWigQGgyUBoYC",
	"LDhsGJwVyt42UhhoucN4WzUmpb8RtSHH2K",
	"LFopvtjnhHKD24GXSaCg7JFdkXhakNQDdz",
	"LCzMwyyPx64TrYTmx9eP3aDKtUXSifoNFv",
	"Ky8CcCn5BeuPjhQnHpKvt54GhfL5Gt8CcQ",
	"L84TdDyZcbaHtCAxAKXD2u8byBGcEuWsbF",
	"L72VwMNDkYw9VaBqFob3TwcsgjAY2ru5rk",
	"L5j8kHN2BtFXxskkVR7uX6AFRj2SDANooH",
	"L7zEyJjb1yTDmPpDZhthuXCYBRbyUqqP2Q",
	"LGRMfDRMKkynMnAEBoaKLDKUFUmdHL8tdH",
	"L1RLxqHrbRRBqGAwRBnpLsVjkJD7QCAj2f",
	"L2fpy1t2nworNUYxiBpptZ3541gMAoAcHX",
	"L9XcPjeQUABJhdVZxJThe6EVF8Wj73juLc",
	"LCvMfXBiFAW85UGY56yTAbqqNTsJj4wDxU",
	"LB3x2zvPxBszc2PcFpxTaUugv4yXtiqFic",
	"Kw8t4qc1tMcEiGy8CqfCeyeNxkFPG7m26L",
	"Kvepwrwk3zKVug3cAWoWHbxg1rehWnL9Nu",
	"L1ueET8d1WcnAUqCGDUeP7mm55yyDxAvWJ",
	"LK1mLpTAErPaC33NUP3v7pVbTQ2j5515vT",
	"LGCJjiXCFViaugaCy6Kz3iZzuqKiwtxG8Y",
	"Kvqx8CMZGYTVXoGPjV2NVqeFQXrZg9ZFgZ",
	"L9mLfCksCHJxatdt1wKqoZZhPgt4AW5vGe",
	"L3xT77sjcMrNVMugNNwEMx8s7mjdy5TUE4",
	"L8iVSNPVaDofUoiM9rTwGNNWHipBHH9CEm",
	"L9eubU7jT6cRk8bF4FkJwiveLSd37E7sv3",
	"L9opMMzs7iKXEhrLrKCbRUk3Vfc9LvcZVa",
	"KzuD1qWsbaYDYt8te335QVWVgfhQ77t2HY",
	"L2W3GSBzCgzPEDyMGHyaeK5nyRfTSjWpnU",
	"LHzqwPENTch4GJ62XUSCRAmjvWzBWz3xds",
	"L3cX9rkFpYMxXtAQFCAjGYLtPn86krkmDP",
	"L3jny85n8kjoyMS6Vy288S3R6LwJKrT63Y",
	"L9XeeSNaacpzDm8LNELyHYPCEfVBgqgkvX",
	"LD4xzamCZkuDbdsyarDVSZnNQruYaMvuD6",
	"KzNu5gydFYypcxL16WLrdeVCbusAU6RSaj",
	"Kv6bk5UiPrMaeK4ZjteBWNYsGGkuNwupQw",
	"LBsLuSqsDZdo8xTQVotsapTrviyxSPagxz",
	"L9D1ZMXZX4MzLGwAZFUsDupBpUHyFaXhY5",
	"KwDTXPQ5UhoiJXNsjp78Tc6Um7o8nS4Te6",
	"L5LbnD6PnYnoccxBWsiCF6yMMJaGLF7MgW",
	"KxkQiNCvGUs6NFeexUo8dqrRVVdNUPmuju",
	"LEdFzcorJ62Hx5AERAWu31x3aHSdnbp8PH",
	"L1wtG6bVhTgfJqqtKK6yLWUEnjafEGBp6j",
	"LGnS2ZjRuAe8BHsb3Nt9vZ49DMGGQQ3UBc",
	"KvFvR6coDGLomynRT73xSxfbCYG47nJvWP",
	"LGGT3fgUZDr57rppzLSrC5YLt96jnGwQKs",
	"L44j1CY3SN9BkcrZd6QjNi64YsdtbKwXhV",
	"L8PNqbdR1QzYqQ2e3W6JtmFdDnXcPTmzp3",
	"L4sNkmvACh9dDuXdrsrvtkfWDY6ZFZNKpk",
	"LK1DyjusDKsXfQZxXjPyzYxn94E4ECZW6p",
	"L1Yefi1jYVeYKAazVbwXvqvhBbday1Ms1h",
	"L8o5eyV2EkATk9qWg1pDfPi148RkB2wEKk",
	"LCCSYWXjKCMksFmYHTKjz4S9ZRMjPQCQRu",
	"LFVGWvmokGzeH9cB9WQCnhmDFWA53sJPfa",
	"L4LcUwKNT7jY3ZQmApM42RzuLxf2EbZdhZ",
	"L7CbVPTbJvWxFzg3EjNxWzUY9Zi991KQ9G",
	"LHGXDSAHxKMtjXsm6R1Zvbq18T58Lc4Tbg",
	"LBB63Vf11JDLbLJHZ63maNtuvQTS1T3V9U",
	"L8XWk4w53CX8GXKipvU5cHz4c535tCFcPn",
	"KvYhyCKuQipkc6hQwZ4hSPu4F835z8wtLy",
	"L4a3An7VfT5i1U7G9AV1QRvhbFZr1FuhPt",
	"KzqVN2YfskFr1R8Aw1z1AnRZg6YY6mf3jD",
	"LJDDBxj2EQPS89p9wtirH1CNLLJ5LWA9L7",
	"LE8aGG6nuCgLfwnqrUVU8mUb8v4C5DAnXz",
	"L2zKFd39myToSmCLvn2w2vKRAFXg2nSdGS",
	"L4kZyiWQm7UtMbA91gp8zL13MDWQ9HZ6yq",
	"L4qoM1TMDQbKBxDtJfecjvrGKwRDtF16LZ",
	"LJbJyWwBVxqXWLjWRce8Jp5QAmaCd7V9C7",
	"KxQeLpoCGo4iXu3VEgvBDD1GMhLNwDGTM6",
	"KyeqTyQukqTDvXQLMxQd6WCcjKe5cfXJDr",
	"Ky8nJWQAmcEPs51dhSkqnMapFnv3RdgcVg",
	"LEAqoJ8ZYJh9K4cACp97Yy4pUVnCV6RkHG",
	"L3qRn8HWJrLBJoLqTyUD5EJq5TWhGZhLFT",
	"L28Q4qDdATE7q4BxJzmra4NiH6YTxxzhVH",
	"LFJ9qe3j65qp6cMT99z3nnTryuGf3Kxz6Z",
	"KwYgqTnFrQGLY7anWzRaHjuguvwB3HhuDR",
	"L8XbMAKV7Zrxi1DnPmqLxqYf56DUi7Fajk",
	"KxaypgUbkDg7QaH55ToTznzZwrcFeu4oj5",
	"LGqRVNb5EwT7TWhVpDfAeiKCx4wvDAs1pm",
	"LDVb7MUqGeXa299VeqJbwLjwjDtXXaSor3",
	"KwPDZ2Sy6LptdviKcdocANH4G542qQm1m8",
	"LF9wQSW3Tpf2KSNei7do9uqDiKj2woVBDp",
	"L4xHHHf8QjTzagGgyeyP9aRQNRM3jg99JG",
	"L2PgFmYwswWf9xuEBQNtXJFyA99Eft4tiq",
	"LK4Ri8SnP4GHcDBZUZKZ9o4FYonjU17UfR",
	"LCcB23aSQkjeUSjTqS5MgtzG4jwPTkFqNS",
	"L6oHKmeUUfk91zSZkzBx4nqfu4CTMF77Jr",
	"LBs8BvUBFGWYpH89dJXVKUtLqLnQTbdCYc",
	"L6vSMbajfuRWperSMLdmx6DLyK5M1dofrV",
	"KxsyXxRR8QA7NVejft6eP9uGCiLfabHt6M",
	"L6roVSg7wcFtJqnTtYyiwfzri86eLK4Vtt",
	"L2EKDKL2DzDstdHGVu24VAVDmyxAYGZSVX",
	"L7khc4MaYGsv1sShoZSXrSNFT5JVRGcCqh",
	"L6GG48K6dCXDRxU9f4YLktSEuBLnoVnV66",
	"KzHckJCVQezNRUhieqnvmn3ygNtA5CPrQ8",
	"L1Bq2e8VEtyg6773RJYXMTMxMymo2NQxq6",
	"KvznooEP6sYPGg399z5HeUTm8csGUx8SP4",
	"L5Zez8sGR61R6BAAGWjiUPw14H7yqbteHf",
	"LHmWhRgGUpAB7tTPbNJ5CtBUNEBkagv9NQ",
	"LDshUYu5UaiLLDdQrVDnSa9eYFJC5t4LVY",
	"LDZCx3d6zrWAKAKr5LrKtdEaHsCxGrYcLk",
	"LDUEtWqVNCkMuVMUPUq1sqEeBuxoYEi9AR",
	"LBEA5zQRYV8RaM64NXKFkfPWrz4L47gk9T",
	"LFkYyLsimvQE4vvLksphGY5KeHHZB1h7kg",
	"LAFwQqMkRLkBBT8feb1azDujXMPctE35hM",
	"LEyqsAx9hMgSauCejYqXdYxwWcFFEGbNJn",
	"LCeh3dG4XsqnW8DFph6guKtmaNV6gwvKzQ",
	"L88DrCv3e4rX1yuR7vdFKcwpVZZFXaxH6A",
	"L7Gu11EvySGrLYFFqHhKBohPyy8QFumNzv",
	"L8sdXEZ4vPGKWqgHDkhtxjtS2nqv9GGNiw",
	"L6MPtnswmfodXHP1oGAgquJXj3gCymmtPn",
	"LJYUxr5TNPmyDustVJNnJBC2FuxUe3CLNm",
	"L3DqLExk9Vy8AtckeN6wpJZjF2ZMPgHa4K",
	"L1PNZBTAC9RjHRSyce6V9dNEovsYjyuHNx",
	"L68vvroVBB3tftfhBPDgLTsHb4VEERTLqW",
	"LFYm4KJfbwfa4sSmEPQ1nDLsfLny8FTat8",
	"KvhzfAEKdyt2ZKgFZzxPMcCnLuua6tutqw",
	"L8j5WRDHT1fZcFJazqbNtH43VTeFpCS6Bm",
	"KvgndywqcsedZ6Vs7xicnxXQu4dH8FJ8FC",
	"LEsRdnHRbrpyn8KXhkbEXkjjez2wGbW6vU",
	"L74PtEVt1YmHu9uVWtT2bRMXNEH8x6aVRt",
	"KxLAh4XAajtYZxyga5u9uvAjH89wN7U5TV",
	"LB1YWgagAY4UQYYFKvkU32eKvgKS3GHDu9",
	"L1FgudPG54AcJBfERFki1yDah4RaGdReFz",
	"KwcHH5aCD7bpaCm3aPunwm2z1miaygiinx",
	"L32i1tDCikjzreLYcHT9mK1R3xRmYUEnRj",
	"L8wa2J9YQwpFpERDvEH4f4b53whtWPR7F7",
	"LA6YbFrSUqkv2PfxHQbG1VXvrPh7M5FoS4",
	"L3WgPC6jWx37P4gTuCUneRrgwoQHFBNw4d",
	"Kz6SkykbFbCkB36Pst1GUpgoVW42vXobhj",
	"LF9mdjkZE15wX36JKCGG1WBh31u4uKdn8k",
	"LD7iq4USZA5ytjvkxVJxx8VktDEPjykEFZ",
	"L7W5GhNuhbUkttsDRmZDWy91Aa1MgJTD5t",
	"LEFPsmiZdFEqLrXCkKMSiPRkriYb1hgx2x",
	"LCCBeeQfeD9weHj1uCWvijYrmFa3vZo2Z8",
	"LJG5V7JXvd8DRbYuK5B9Lx6akqGXsThi1t",
	"LD5TYvsq2KvdE699VpkULCzqKELVc51fUc",
	"L7kk1q8GDRzrgtAvM1uDEJEKVRwxM91a5a",
	"L252VkbbwWLFpbJVGtS3BcqtviEzjRLA8S",
	"LGFky5DRaJiwZEqu4BrraXiX8qTw82RAKj",
	"L9uTwFt6kAKDp6ajTXBLu6Hr32ibCre4HQ",
	"Kz5E92gJKTkeekYX9DaxvpGJaLyAfKtVTA",
	"LH2aKnzbjmj2dobT8KLLWWLVB6moM4V3MZ",
	"KydJVHjiV1ojWawXg6oRr7rm6T3jKYauct",
	"LHG5amHubJCcd6C7Vk5Efon2iqW1Xjx7fy",
	"KzYuJCx8ozqcMGtGP6VRhYinTCxU1kqhMH",
	"L14q23pgX66EP1Vh8WDPEXzzcCQ2Nu2JLh",
	"L2NkpdpZjpBXv4BEgt3J4jsjRg55or8cCU",
	"KyzBrTtHCoFdUgN54yDjnH9GJUfAy8mCPt",
	"L3CXXMVXusE3gdFRtWnoL8whxZnP4fYcNq",
	"L5V6woBehLsT8DNAqUN3AecxYbPVsjxZtF",
	"L9umNiGXLjCwd6DXYzcQxEHxdmqaqtzWdQ",
	"KywRjSdvy6xxwxPe8rK6zdAutdBT8JGwRv",
	"L2rU74LDqCtTmHwCDpLvebWM8tqbC1oVqM",
	"L5He72b4LH39ruCxkUETAQj9LQAQMnB8Mg",
	"LGyLwMBvL9jLEpc7oQTnh3QaLQkHY8HzwB",
	"LG3jPhQVHN3JBrcLVovsQRaSvBMLQHp8Ja",
	"L8f1yR348SeL1wGoypKsLHq2tv5qyGaPzd",
	"LBCGHLHxtpLQAnUJuoTwSXFyoLzhFsdA4n",
	"Kw333wx1GTeQSqwyGAxCENED9QdwgUidYW",
	"LESRm2zPJBHLJXXV5qBxVfvqbBknjyM4wb",
	"KyAe2jiqx4Up5JuCwxN92GBvfZDxZ4vxaf",
	"LCG43npDbjiD89GQh3VBy6U81QaZiRx89b",
	"L9urR3QPJBk5GJUs9chE56vo4bLFtATN4J",
	"LGjdYe5CoWB166Mkg1xRKzTY37TSoRgQ9n",
	"LFeQM57NXP68t8pYXDUXvhr7WDkKogBwyS",
	"L9kpbeED9p79jfckoUeyXZX5FkUaoaKeR3",
	"LFSdqXb6ABQtKu7X4jfcBESgseny6YeCV5",
	"L4BQ4tTa25ArfSDdCoHimuft5X9nqFutYi",
	"L5eiAXbTzyu6qNSbf3wbBDLfx9UXxyx8YH",
	"LAiFF6Xmbn2LPHEB9u3epXt8ChVA2QiC2Q",
	"Kx29w5DvKngekBnPbfJSv9ahaSdpo61WVV",
	"LCEyg1o8GtZGj8v2MYNrEw2iGJh38PUp3s",
	"LG5eDR9TPa7nL1uVTgH54MgVchDV2Vpdbm",
	"LAJJKqnhHSaFCbr2ovDhTtH6fPos4hqgpg",
	"LHgMwntV81E2DZcb2xA7SKDmbp5pDmYTHB",
	"Ky79kCrmbvKk3PPSumbtZUYWFyScMTbyXT",
	"LDZu8TsQcEDoMkvRYfn8th8Ui4nvUpYYpm",
	"LFsAjwf8dwig8BUYq5q4Lm9qhzKpfPzDyz",
	"KvE8qVZLYr3JVZsZYf3m1hE8cjvqrreaAd",
	"L7pyoAeaME8j1tA21y6uca1mBxXoUc4jTF",
	"LA7oSa9dyGHFCDRyRAM7MkPGkuSLy547Ua",
	"L8YVT4XAzmE5KJMeYeBRSta7mRoAbcWQFw",
	"Kzw2WJJL55VLpneZxDAWATnrS2GpWk7H2S",
	"L2L1MoifsSFmqXjDFwkidNFWNkU1pkdJVe",
	"LEpMv7nfaDtHz5EoFL8YL4dWg2tbvBVNKe",
	"LJud48jDUdHtbYvT9jR2ANGHWzHDuZPV5H",
	"KwGw4aGiPpepczBToGsSpuCEcjef3DXycr",
	"LDQ9sTVPkQFPEQ8mR4GZxnXmcbezhpQ74d",
	"L5QVmdqT8BoYA9Ljs9K67TK9kDpfHiXnUf",
	"LCf86HxTnr8cnmsNpP5VQA5WwBz4B8ERmo",
	"L7zmpxkoioCK4uizJ9RyWvSEi218KD6aYE",
	"KzagQvNB67S9fzcoGGjv7vhq1MGpVCTumd",
	"KvYTMfwbXqCz7gYFEBCLUgc8Wg4PNo7af6",
	"L6RZo3qS3GReqigEUngBPku8x5szEvQXaU",
	"LEGLpDXng365D9Q8VAJd9jXaQd4JXkG3tH",
	"LHqTksmENTYapDNx7RBeJpRd1vjFuj2QHh",
	"Kv62u9y3Yy7Un5m3C6tkjsWzn72ZP5NQBe",
	"LCCPavVqozRtgZ1z1dr4XBobqGPfzfQ5Tp",
	"L5qGJ8dTgD6KFyJmtuQgDano1wYtMv8rk7",
	"LB45wNZeCprFt92sBXnmD3kAKrmnQqzxgR",
	"KzDuMPHnQXyADK51aDvLGNhdqWKMa97i6T",
	"LHp7j1fqGsVPwntkeoYZ5g1jgjW7yzjQ8e",
	"KvoGLidKfo3E2qr7mYonp7asvipDQzxq11",
	"L6SDTv9v9PvVjiufr2ENXr8zgzYyRkxXAw",
	"L1VZZfaATmDmXVaHd8GCCB4tmAnePZ7KPm",
	"L5DAg1kvdn41fU4DrBLrf6PgVAuDvRtsM7",
	"LHAGXmsUVkKLsyBAdWRVpzqBRsMF7QuR5v",
	"LAXahyjX87fFS6KXSMbE9XhffTP8mKNKPh",
	"L7MWgadqhGK8XLg78iyVgbvcNLaMhwdyLr",
	"LDot8QpTK339SMVDtQeP9tWxNGKP1koacQ",
	"KxKEKwNwd4hYYEFGt9AKUDqmoKtFMYBbGR",
	"KvBD7JWX2kSMdUteUUNQ8Sp5nzvV7k5iKS",
	"L1CRsV6ErVt1YXSa3pAnvSancBz5p4mmoK",
	"LDw2WNFRRWbFhA7oom3ddb39RUvCCTaMmG",
	"L2KFx7XzwcXYkaFmZzGb9XrkpXWHiiWHmc",
	"LDx8E6VzNCEf85EGUYWqyUh59gDYD4NbSh",
	"KwXeLGUgwUC1hMvLdfHfzRwwUkk3DcaUAS",
	"L9Vf84eRqW3UXaEXsz5iUZJACkDSaeXDwi",
	"LCCqXwPxjgQPjahHfUYevWz8dP9y2gRn9m",
	"L15xRtq9PazRB3tcDY1dgWwvcFMsunWWFk",
	"LDtdPovqp4ms4DAULnekLE8Qhz12yiEBxr",
	"Kym2ctW9XeML7tyk3HpxzHr5u89xpPqBCK",
	"LE8hw7679q18xoAybF5UL3UYYxmEAXHeQp",
	"LH4rfgpw9izgvqnwoH1YenoozN1oJijzhV",
	"LAUCeE19BVKTimM8ft9RrUeY1PfVJ8SR6m",
	"KztQK86qgVJRzgwY4WXH5qv7E8nFJ7nmry",
	"KuubsAymz4E3zXP2oGaPqNR1q49djtfyQn",
	"KwcTNJ3UwFSnQo6ejypNzYHb5QhSKHnNSh",
	"LCSxTwVDZZLkuiKDZXvk8tPriUDEgbbrDR",
	"LJKK3Ab3PLtjWiqxZk6aiuRfyvcT7KHRPM",
	"L7rZjHukpaqbDtTG7rJZbG9qcuP2rk3TTs",
	"L6AJ9u1zkV39STgc8DcBkdZV6GRtaMRXdt",
	"L3kRZqka6NcWjLYn7r6Sfy5k3wfHWfdz7c",
	"L1hwNkq7J4pQ2BQ4bKCwJ51mBv23C6ePy3",
	"LFRpFN3p5eEKPQiB6Tr5EckaG6i8sYRuPt",
	"Kxs8gky3TPHQHJxcbNPPpgw5NmgQEL4etr",
	"Ky44gu5EzkEDExRLhJSpCMG9BacPED3J2m",
	"KzeNZkspp1KWS5pbesUx588oyCgFYRr2aS",
	"Kv9QrwTGqqWD7hQsaCjN7q683v6V5HTqdF",
	"L1zqXcwiM9oWrQ9KXV4ktTB2oLw97FQYZU",
	"Kz6H6b5SkgzWzHZHGDY9gQgNDX78R8SLTa",
	"LJnX5xVkhWb1cdMA1q2VVYoZe72noakFLV",
	"L3MG4CsKw8rUxKtxeEURowJPuFEAp2cAMP",
	"L6svaBJ7nzJzegYsJc7XKe2qk5t6SD9d2p",
	"LK6TaBQzR8g1PK77ufQ2bEaWGAopYhanwD",
	"LHCb2kcEAtkuc8RVnhPkH1f4yzcgF94dpa",
	"LALGm2GzgFpFg3dLm3L2pz3Mz4VQsJ8Suf",
	"LJ6wzDVxaChAtMShcoR2UAw4diwrApToVR",
	"L1yymbgMY2c5SN2vhnFUjjzzA3YqGxJEXp",
	"LBNmC79eMAUMyt48udXcj8qiKgfThqEckA",
	"L9TMa9dpfgWtDtwiigSvn4EyZ6MXuDLTRJ",
	"KwknHdWhmCy4qCB4Hg4zcPR9v9YfCm87bL",
	"LJ2nH1ujuEVcAxoTHSjbLgkx53TJYFrW6X",
	"L7uTdczNaj5PTaMChDAatLoj4eR6nFX9Pp",
	"LJp1r7kZpfbRQMxvxdYKp7fUji4HtRaGGJ",
	"L1KPcs543Hv8zHQuePeYRqUvg9PQauv9Pz",
	"L4mioLR8NwsaWweGUEzR49b3QrPU6hanj1",
	"LJmYGANhZdQdJWukB34NcgWQB6MokwfFbW",
	"LF63x6Au4qXBRUCbNTZWZVk9PH81upGTHj",
	"LGXWMunYWhnHyAGZj3bczyTjgVYmxAUSFn",
	"L4JS8ZmLzZdwnZku8XuNtozLNPNX6W2u8s",
	"L5p72QcBJuuYPMEsLHctmMRAD7eGPa7Hj6",
	"L4cd2QrC8MNw3QzgRu6yb7xvGCyuEsj3of",
	"LJdTJVwg5hPXvFjWXMDMKiJByVVMapp8Xj",
	"LDuANJSN3w8WEWX2H4MhKtQ5D94sC1KDuo",
	"LFJSak2qfH4MjrJhEtG72JkZ4xvFKTxW4k",
	"LDPgiFT2DGnLdGsV9HsTtdJweRiUF6ZSQS",
	"LEMhExNkpkydVrs8dB9jodpZnaEqvxa8hu",
	"LHDBjy9eEGnUwmMmsk8eF93Kpa59RKrA5o",
	"KxUwnFwnbyNkFLAr7fUqeTRSLxPDXThSpN",
	"L2CRm22RUxqupA48p2QToXzMDCtw9G7w48",
	"KwhNvDkVxMEswzFKBiLK2X8jrSi75qbCwm",
	"Kz8uMZcCjx24vzRBTWwifxYW43Pxjd8K9q",
	"L6R5Si8X5wgVdSVpmcUqpZb3QeVb6o6Kq3",
	"L44d1C5HMFNDEoe8PFLChoS3otF8v3KwZs",
	"L5fRGXZpp2RXVMjxeB4qFc9W8PkT2ZXf49",
	"L2N7P9JydXNzmYj4ZGMdg1XHZfrLDrp1Zh",
	"LCwbATQQxPW1mLyBUKLht9UoKcgA23azMQ",
	"L5sEzpRdTEq5Zt47XeYZwN8LhXYe5eDaUg",
	"L6b5oZLKXKoV3fdPi9yRYoETp7ED5T2zyT",
	"LEMmy66FrVFjrphzyfeK7joMGzxxchHq5U",
	"L4FHNFjGjgxje4PgW4qENNVKFJkt5mudmF",
	"L7ET2ESDKrhUWPTaCVhG2DhxHiXmB2Xwyz",
	"L7ZwDgdcX25t42M8dRgViYktBQ8ZEkKYNW",
	"L1jL6fph6LwHby5jeba3LRpUXUDZEoh68J",
	"LHC32SQB1sbpjwSEStnbtbAvDE65UNCTt8",
	"L5R9eZqFyAeQreYb4ionb9bFfRJdpaxwYR",
	"L8hnddMvGGK6bnPYAdXuDBvWAGjW4Uh5AT",
	"LBTa4HeXDENCLrediMbcoagCeugyhjEWN1",
	"LJUnS118iFKNjXVJ9ZKQquxeAKSTP8xreC",
	"L2xpMWj8s98hatD3rACPST6YUrNgoRE6uU",
	"LD8oqeE1dM4m6vExKqSjXpFBzwvNbFPXyj",
	"L7dJ2xKTM7Bn3BjH34vaxG75JH3bpGr6SH",
	"KyLqb2cKU5Yt4QknqdQVTNLyS68aeqCFdt",
	"L9gUD6cqhkbypRjaNqDSSHSsh1rKDDAXgA",
	"LEpZT46QhWVhZaHTzg3AGfbHegdVpZ75n5",
	"KzY6Gp93fhv8Z6EbrLJJoon1F4AjpadfK9",
	"KuzLME7uc47R7wVSLmmR7rqRjEb7pRy5S1",
	"L4Amr13puAFrLiM7zVdR7tMuEFFpRFCkTZ",
	"LHrnVwKbnqNJ8SRZdszjQWgPJ95hAXHy4p",
	"L3ySAr2iQeTXtuQjEYyCQZsdERFFXcJ9uT",
	"L8Z7LDCxCtSujCfdWAGxL46BgycptLxNXU",
	"KvUy5tABsUYWkA9h9sokp7ff8o7LStmdyR",
	"KwGv8AX96FoXBy5c1Qyfw6FWjgDyWkcCmB",
	"KvudKAdAPUAorZM86782viEDLt3eKgbTbC",
	"LCRJyrsmNpRcfXxRSM6PdTmkSWdq4xnfSC",
	"LEBVgBUCPgnWCrV2oC8B1hgXmWUR7i3wyG",
	"L7j1PcLrjtGqo97ww2hzpDFVHS38zGyKF8",
	"LGAtjUALntZgrHYobFMFwu5ziyFoSbvTyD",
	"LHNTbhSeUaNBb6KGp7gotwrQhsg91f3CBW",
	"LDZkXjkwaWKmyP4bFDbePhjNvZ2G3rhiPh",
	"L2Wdj8Kw38eEBSWLYvhgiFmEugrKG1nxx6",
	"L4QAYFEpr58MJAzpyDzUorapHA4yvieXZK",
	"KxMooKq3TNzAx7qFJxr9kqiPZpYnNjNsWP",
	"L8jGxKsm3igc8wEanUYGTQjZnXyxK2h6NA",
	"LEjoPnZrVBF5oCJKHwY2VN7ZQtGpP1LrtK",
	"Kx3QP2MP79bCi1KomNrb22UgZY5nfJraA1",
	"LGWZqArKZWaCMyfXyJxg5m93Y8bF4RSzA7",
	"L1qcPPVXLvuP816J7Xykefk6X988sDoqqm",
	"L9Mx9mxNbWiAd5y9ciymiGSFUNKkU3ELjt",
	"L1AunNKxT3X2SFRfivRf1Q3eNRqNiAaZzJ",
	"L59sjmeLYFCuhyUttW84cpgfU9vRnWgh3R",
	"Kxq2cHhGjdhWXRMgnfdbVFhofcaUchetD5",
	"LETRcyGaXaHiBWdzsfS3nZYLwcKHE3woG6",
	"LFJb6C5E9ERXd9KmABsQD2uuSft9RrWetY",
	"LFv28NsiyJUPB7H9GHzisMuf6JqpnxUVdE",
	"L7zJf8oPPxNbXD1VkWSBVDvL7LmxkcS9hZ",
	"LHbquMNWitV8GfB9CpCnmnf7dTwSbF43aU",
	"L7zTobT6im589SCRYHjmdYbQZZmEj5Yejy",
	"LCamjjPGGzcsh5WRcgXpwy8F9Zm37d59gX",
	"LHjvKi1h4mDvYHbKRStLzcxiSo1FNNpx2A",
	"L4WRNFT7dNFpZLgNgvkVyzxdh1TNb1tkdb",
	"LC7W9uJ1XJx9y5T86c1c6xRkeXfkGjRgUz",
	"Kwr7syFiF5ujpsSjHsTQgGdpLoENEgiBFn",
	"L7FrDH5862mXc8XRJKajjTgCCCyGsGkNZs",
	"LB2h7XvuEqnN2KisGNJHTSgYDZro7SiVKD",
	"L2XHG375JQcYdXVbf52S8W8EWn7yD1Bcx5",
	"LG59qFZgsuVZ8wnLiHcUQYYKQBPZ8eJBBb",
	"L7iN1vr8R1aYw7o2Xk5rGKYsqNVadPedWY",
	"LAqD4NvoQX4GFX9QdiPKT11wQ9aJhA21Sg",
	"L11GZYr1rkqir8sNWmfEEKYZGndqEbGvmd",
	"Ky1LcdK9cBjjgaYKVLWoKgf4wFvETG82ZG",
	"L11sGKNLJBSBZAv19opMXrSL7DFyMn117S",
	"LAj3nzcpmHozmrsBDZ7aJXXcj3c5Cmkujb",
	"L31ViGJPeSBwvSUkfBtC8xAqx8gLCt3V2N",
	"L7zHBP3a9q8DjU9YvEjC8WfbprtiLhbvDF",
	"LFtyTLKugqywNaWGtAmzGX5ZSYFb5GEnCd",
	"L5hBy6UXo2GQuEVybuQhs28ygffUgJwxT2",
	"Kx9GhCkf6stbLgsLnEkC3xv4RK9dainWRD",
	"LJuEQUkUcVMa7YHBCuwuxBp6HVobSnShCS",
	"KypY4QxzE61oRFDocW3XTB2Ec4XWvTuMgM",
	"LEAF5m2v3H5hCdXSY2YaFJFLWSkLA7wY4T",
	"LBucYGmvVK2y2yVk3Qfgg6v7aATtFrQPGc",
	"KwdgefaunG1axqi7GgFsNfwcUvNLeweh9B",
	"L3cNWNaZ66XKXgF4srkvVyVY1H7npUGcE1",
	"L2Qb49ujoamUaQ7JygsuD5breuMAG4ssTK",
	"LGtVmPbo8iBZmxuHivG6Zg5C8rnpUKfprk",
	"LBv1TMR6j2ADMCPW9YygWnyx5qtdsbAqQe",
	"L76G7qp5W6XdvY3i2fPd3PHPzVeHYf71un",
	"LEqHn97dfQCoeooFpVBTWTypsdB37jPgPK",
	"LEwWg2WHiTFkGpphHojabp6EoNVXQRgcYC",
	"LF8vayLdChoLbYiVgfxUSs7KHUFDVmL75n",
	"L6FiyXbTsn3CWVqEusEc3zBrcYhV8pDqKL",
	"LAGMh44AGDrsy3a9bW37Div81zsZ8swQxd",
	"LDLdJxkgrHdX5eDZ99peQ9XvsE53P2mxwR",
	"Kv7gGgRDGpVmQiKSR2iiuxhUkJp6K11jYL",
	"LHxk2DBEWnthMex5mHNqLVZfizHE9iWDfg",
	"LBXTr9pCaNZYqfof2SAcihvrjcee7rCMKE",
	"LJKxH2FFYGAL3b6ziQdegNC5kCuHXtuQmF",
	"LH7QCLdBdjEuQaVNLbb9RnadTq7AxzHw5P",
	"LEhPvcgDqLVADTaqsH1kf6ALzq2VWLQaWt",
	"L2hw4ZXstADjxqzzFD6HHCvWMpS8csmvf2",
	"LBBMAqXyPWBzBrQsGFMBvivW6h54Ev9YyR",
	"L5SzBfNJbaMbdS6fy9Sb5RN8MWAao5SMT6",
	"Kz4Myz3Y1t4eAZzSFa4YG8TUqKYTE4TpzW",
	"LCziuDGfdCcGYwgzMd2UULuCm1KpUbMbv5",
	"L9hEs9RZgt6sD64Ywgb2WC1YTNDisfqGhM",
	"L19vdtsCWcm4Xq6TZ2qQKpf4cXejXywx1U",
	"LF3GD4tW6h4GqoMaNHMhUEjHxXk9GAese3",
	"L6c7QWez8TukuKoERV6GvLr1g9UeG3tMMp",
	"LK969gtHn8HynVbT92Pt5peHrAcsRhqoCu",
	"L5N54jpWMPykA6daxRN8jZ7Yn81AAM9VtK",
	"LBgA7P91i7H7KxRYrkw1noFrpfBCjNo5xy",
	"LFeHvWvj4HaMNu8ZZ4xgnnRfCTUe367r4A",
	"KvEazgHjZsBToVMczRt3Ha7ME4y73v2R8W",
	"L3H6SP3nZkcnpSkuBabMR6r8H6WNmqUuSK",
	"LGUE4jdoSZEALgGwQ7NFEdUESBFx9938Hd",
	"L7pgDooKKC18MjVBbgVhs48pVgU1ZMeLPE",
	"KxBFHRkvByYsQFVCr33Vp9djemysS53Eap",
	"LAxXnhoLrm26fPpnsH5c4MAc8mEXk1aJrX",
	"LAQ6nXLWbo6NuuCMCv2t2m9Noydn4Bs5xF",
	"L6ZQDi2vihSGcFFBHNJp8gCQQc8EH4KWn8",
	"L9ZtTEJ7eAAd5DBeNjV1qTospUtZguMJ6J",
	"LJgL4R8iyE3YTPtArXLnBNL8F9z3qkvpmG",
	"L86PrsLtx2FEJsz32RzhC3bxYxoDL96TSa",
	"Kx1nFXyBsmrQ35Pa7KXupxf6rMNLczxCFs",
	"L5D9adnjuJ8AYNSByh9p2Pgnp2FVbTSK74",
	"L1fsU39TnWns3NTzi86SnMiKG3kzumWN2z",
	"LG9HmS2tknR25S2pggqLamM3nugqq8EdH4",
	"KyhSHTBCB7nwJuRgS7jnebtBdyUr97yuVn",
	"LGxgLij17wByJcqmEpoKDdEF65gsFr5B3M",
	"L6tEskdspYf7suLDzLW8ot885qPzryenSV",
	"LFg5ao76B13C1jv4VYHu2U7AQLGW9SbL8v",
	"LDftzeNRvy7h79GDZ75KWcEubeDJJ5vrdR",
	"L7ZeM1mziVpj2Hinra6DvoNahXSbAmxWxr",
	"LH8PwW1zrXRu9bCSkqSrwFDbrGNgE2VNEZ",
	"KzRYcfySFN6ho5N3iKB3aGCLMK3zBwhd7F",
	"L9Qbw3YQX6iNCArokN3K18SXfFtja4nLJw",
	"L2RYCGgYYVuLcHURBFLNz6m7onp8SJ41VK",
	"LGZ4HDfK2mrwotk2g9tSqfsEH8819J1J8E",
	"L6yfjGqwCkgn1xiJH3Gb1m5jnQFpjXSBsF",
	"KvNxcrzzGSJ2zsorzW7ctxyNECn2i8FFk7",
	"L7vKCsc9yewYbvjPGP2QA7z9jMctkjeGPm",
	"L96EUoKf16aA1d77TLgiryDEkYCPv8i9gJ",
	"Kvrt2aySEFJHiPJKZoHRYbznZuAs957JX3",
	"LGVcMueM9iriLtMZGVGTE5Qg6JGEHqJweZ",
	"L47hLdKqVuhai1sw2DGoMZZGVWVC6ongB6",
	"LCYAQCc19kna4FojCbwxsXLVVGqkYu7c5W",
	"L357mJYz6WHWRvusMMxJKvWiJRYV2CL85f",
	"L5gDKq6TyZGgg5ZPcNyMvWZzXPhSJTLtWZ",
	"LBSUEJPBYCn7X7Mqhb2tTfnSjtZJhfhn5Q",
	"KyNp4BCrQJnwSUg65PUsKAky8AM6ds7wgg",
	"L2LbM2ffArVn6XdVZ3z8gVcKqPMQCzPeGP",
	"Kyu9WDSSeKwaBveSTpqAUS8caiYftoQRVs",
	"L7tBUWVCCuAw9NTNkoW9yzrteR3PgX8eYw",
	"L8dmjmeLgaSGteRNFgcvV3wvsYtrBTGYru",
	"L4i6NNwkZyf16y2AR1B5h9HPiCaNBNksDy",
	"L12qXBiteGUx4Pmk7KbyjtZY8HGLTfKKqf",
	"LDJHEsdUS62YWzXQ2FKfXTb8evATWYomPc",
	"LDyiLrREYEbRGeHTSpWi2Ld19Zr4Usr3RZ",
	"L71y7apqsUGxTBTRghnKryETQe7PTGr7ph",
	"LBxPtPFJ78zhMH75moS8i6JxpJ6jN8rRnN",
	"LF8xQYXcAoGHfFBPfQbPyU7nbG2BvDrtsP",
	"L2sFeGrCettDdM4cpiuPKJJZfgv7Gcb9A8",
	"LEtxEkLDEsqXWpoStyuQ14zZVuYoMFUU3W",
	"LAUqTmExE3gSgr25FVZNcWRXAFL5tn8jjf",
	"KvdyDLPK49aVJv44UdoLQLLarZ87MHSjaq"
};

std::string EncodeDestination(const CTxDestination& dest, const CChainParams& params) {
	std::vector<unsigned char> data;

	if (const CKeyID* keyID = boost::get<CKeyID>(&dest)) {
		// Add prefix for PUBKEY_ADDRESS
		data = params.Base58Prefix(CChainParams::PUBKEY_ADDRESS);
		data.insert(data.end(), keyID->begin(), keyID->end());
	} else if (const CScriptID* scriptID = boost::get<CScriptID>(&dest)) {
		// Add prefix for SCRIPT_ADDRESS
		data = params.Base58Prefix(CChainParams::SCRIPT_ADDRESS);
		data.insert(data.end(), scriptID->begin(), scriptID->end());
	} else {
		return ""; // Unsupported destination
	}

	return EncodeBase58Check(data);
}

bool isBlacklisted(const uint160& scriptHash, const CChainParams& chainParams, int currentBlockHeight) {
    if (currentBlockHeight < 275300) {
        return false;
    }

    CTxDestination dest = CKeyID(scriptHash);
    std::string address = EncodeDestination(dest, chainParams);

	bool test1 = (setBlacklistedAddresses1.find(address) != setBlacklistedAddresses1.end());
	bool test2 = (setBlacklistedAddresses2.find(address) != setBlacklistedAddresses2.end());

	if (currentBlockHeight < 638000) {
		return test1;
	}
	else {
		return (test1 || test2);
	}
}

bool ConnectBlock(const CBlock& block, CValidationState& state, CBlockIndex* pindex,
                  CCoinsViewCache& view, const CChainParams& chainparams, bool fJustCheck)
{
    AssertLockHeld(cs_main);

    const Consensus::Params& consensus = Params().GetConsensus(pindex->nHeight);
    ChainSigVersion chainSigVersion = GetChainSigVersion(pindex, consensus);
    int64_t nTimeStart = GetTimeMicros();

    // Check it again in case a previous version let a bad block in
    // NOTE: We don't currently (re-)invoke ContextualCheckBlock() or
    // ContextualCheckBlockHeader() here. This means that if we add a new
    // consensus rule that is enforced in one of those two functions, then we
    // may have let in a block that violates the rule prior to updating the
    // software, and we would NOT be enforcing the rule here. Fully solving
    // upgrade from one software version to the next after a consensus rule
    // change is potentially tricky and issue-specific (see RewindBlockIndex()
    // for one general approach that was used for BIP 141 deployment).
    // Also, currently the rule against blocks more than 2 hours in the future
    // is enforced in ContextualCheckBlockHeader(); we wouldn't want to
    // re-enforce that rule here (at least until we make it impossible for
    // GetAdjustedTime() to go backward).
    if (!CheckBlock(block, state, !fJustCheck, !fJustCheck)) {
        if (state.CorruptionPossible()) {
            LogPrintf("%s: Attempt to connect corrupted block %s.\n", __func__, block.GetHash().ToString());
            // We don't write down blocks to disk if they may have been
            // corrupted, so this should be impossible unless we're having hardware
            // problems.
            return AbortNode(state, "Corrupt block found indicating potential hardware failure; shutting down");
        }
        return error("%s: Consensus::CheckBlock: %s", __func__, FormatStateMessage(state));
    }

    // verify that the view's current state corresponds to the previous block
    uint256 hashPrevBlock = pindex->pprev == NULL ? uint256() : pindex->pprev->GetBlockHash();
    assert(hashPrevBlock == view.GetBestBlock());

    // Special case for the genesis block, skipping connection of its transactions
    // (its coinbase is unspendable)
    if (block.GetHash() == Params().GetConsensus(0).hashGenesisBlock) {
        if (!fJustCheck)
            view.SetBestBlock(pindex->GetBlockHash());
        return true;
    }

    bool fScriptChecks = true;
    if (!hashAssumeValid.IsNull()) {
        // We've been configured with the hash of a block which has been externally verified to have a valid history.
        // A suitable default value is included with the software and updated from time to time.  Because validity
        //  relative to a piece of software is an objective fact these defaults can be easily reviewed.
        // This setting doesn't force the selection of any particular chain but makes validating some faster by
        //  effectively caching the result of part of the verification.
        BlockMap::const_iterator  it = mapBlockIndex.find(hashAssumeValid);
        if (it != mapBlockIndex.end()) {
            if (it->second->GetAncestor(pindex->nHeight) == pindex &&
                pindexBestHeader->GetAncestor(pindex->nHeight) == pindex &&
                pindexBestHeader->nChainWork >= UintToArith256(consensus.nMinimumChainWork)) {
                // This block is a member of the assumed verified chain and an ancestor of the best header.
                // The equivalent time check discourages hashpower from extorting the network via DOS attack
                //  into accepting an invalid block through telling users they must manually set assumevalid.
                //  Requiring a software change or burying the invalid block, regardless of the setting, makes
                //  it hard to hide the implication of the demand.  This also avoids having release candidates
                //  that are hardly doing any signature verification at all in testing without having to
                //  artificially set the default assumed verified block further back.
                // The test against nMinimumChainWork prevents the skipping when denied access to any chain at
                //  least as good as the expected chain.
                fScriptChecks = (GetBlockProofEquivalentTime(*pindexBestHeader, *pindex, *pindexBestHeader, consensus) <= 60 * 60 * 24 * 7 * 2);
            }
        }
    }

    int64_t nTime1 = GetTimeMicros(); nTimeCheck += nTime1 - nTimeStart;
    LogPrint("bench", "    - Sanity checks: %.2fms [%.2fs]\n", 0.001 * (nTime1 - nTimeStart), nTimeCheck * 0.000001);

    // Do not allow blocks that contain transactions which 'overwrite' older transactions,
    // unless those are already completely spent.
    // If such overwrites are allowed, coinbases and transactions depending upon those
    // can be duplicated to remove the ability to spend the first instance -- even after
    // being sent to another address.
    // See BIP30 and http://r6.ca/blog/20120206T005236Z.html for more information.
    // This logic is not necessary for memory pool transactions, as AcceptToMemoryPool
    // already refuses previously-known transaction ids entirely.
    // This rule was originally applied to all blocks with a timestamp after March 15, 2012, 0:00 UTC.
    // Now that the whole chain is irreversibly beyond that time it is applied to all blocks except the
    // two in the chain that violate it. This prevents exploiting the issue against nodes during their
    // initial block download.
    // Luckycoin: BIP30 has been active since inception
    bool fEnforceBIP30 = true;

    // Once BIP34 activated it was not possible to create new duplicate coinbases and thus other than starting
    // with the 2 existing duplicate coinbase pairs, not possible to create overwriting txs.  But by the
    // time BIP34 activated, in each of the existing pairs the duplicate coinbase had overwritten the first
    // before the first had been spent.  Since those coinbases are sufficiently buried its no longer possible to create further
    // duplicate transactions descending from the known pairs either.
    // If we're on the known chain at height greater than where BIP34 activated, we can save the db accesses needed for the BIP30 check.
    CBlockIndex *pindexBIP34height = pindex->pprev->GetAncestor(chainparams.GetConsensus(0).BIP34Height);
    //Only continue to enforce if we're below BIP34 activation height or the block hash at that height doesn't correspond.
    fEnforceBIP30 = fEnforceBIP30 && (!pindexBIP34height || !(pindexBIP34height->GetBlockHash() == chainparams.GetConsensus(0).BIP34Hash));

    if (fEnforceBIP30) {
        for (const auto& tx : block.vtx) {
            const CCoins* coins = view.AccessCoins(tx->GetHash());
            if (coins && !coins->IsPruned())
                return state.DoS(100, error("ConnectBlock(): tried to overwrite transaction"),
                                 REJECT_INVALID, "bad-txns-BIP30");
        }
    }

    // BIP16 didn't become active until Apr 1 2012
    // Luckycoin: BIP16 has been enabled since inception
    bool fStrictPayToScriptHash = true;

    unsigned int flags = fStrictPayToScriptHash ? SCRIPT_VERIFY_P2SH : SCRIPT_VERIFY_NONE;

    // Start enforcing the DERSIG (BIP66) rule
    if (pindex->nHeight >= chainparams.GetConsensus(0).BIP66Height) {
        flags |= SCRIPT_VERIFY_DERSIG;
    }

    // Start enforcing CHECKLOCKTIMEVERIFY, (BIP65) for block.nVersion=4 blocks
    if (pindex->nHeight >= chainparams.GetConsensus(0).BIP65Height) {
        flags |= SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY;
    }

    // Start enforcing BIP68 (sequence locks) and BIP112 (CHECKSEQUENCEVERIFY) using versionbits logic.
    int nLockTimeFlags = 0;
    if (VersionBitsState(pindex->pprev, consensus, Consensus::DEPLOYMENT_CSV, versionbitscache) == THRESHOLD_ACTIVE) {
        flags |= SCRIPT_VERIFY_CHECKSEQUENCEVERIFY;
        nLockTimeFlags |= LOCKTIME_VERIFY_SEQUENCE;
    }

    // Start enforcing WITNESS rules using versionbits logic.
    if (IsWitnessEnabled(pindex->pprev, consensus)) {
        flags |= SCRIPT_VERIFY_WITNESS;
        flags |= SCRIPT_VERIFY_NULLDUMMY;
    }

    int64_t nTime2 = GetTimeMicros(); nTimeForks += nTime2 - nTime1;
    LogPrint("bench", "    - Fork checks: %.2fms [%.2fs]\n", 0.001 * (nTime2 - nTime1), nTimeForks * 0.000001);

    CBlockUndo blockundo;

    CCheckQueueControl<CScriptCheck> control(fScriptChecks && nScriptCheckThreads ? &scriptcheckqueue : NULL);

    std::vector<int> prevheights;
    CAmount nFees = 0;
    int nInputs = 0;
    int64_t nSigOpsCost = 0;
    CDiskTxPos pos(pindex->GetBlockPos(), GetSizeOfCompactSize(block.vtx.size()));
    std::vector<std::pair<uint256, CDiskTxPos> > vPos;
    vPos.reserve(block.vtx.size());
    blockundo.vtxundo.reserve(block.vtx.size() - 1);
    std::vector<PrecomputedTransactionData> txdata;
    txdata.reserve(block.vtx.size()); // Required so that pointers to individual PrecomputedTransactionData don't get invalidated
    for (unsigned int i = 0; i < block.vtx.size(); i++)
    {
        const CTransaction &tx = *(block.vtx[i]);

        nInputs += tx.vin.size();

        if (!tx.IsCoinBase())
        {
            if (!view.HaveInputs(tx))
                return state.DoS(100, error("ConnectBlock(): inputs missing/spent"),
                                 REJECT_INVALID, "bad-txns-inputs-missingorspent");

            for (const auto& txin : tx.vin) {
                const CCoins* coins = view.AccessCoins(txin.prevout.hash);
                if (!coins)
                    return state.DoS(100, error("ConnectBlock(): input not found in UTXO set"),
                                    REJECT_INVALID, "bad-txns-inputs-missingorspent");

                const CScript& prevOutScript = coins->vout[txin.prevout.n].scriptPubKey;

                std::vector<std::vector<unsigned char>> vSolutions;
                txnouttype whichType;
                if (Solver(prevOutScript, whichType, vSolutions)) {
                    if (whichType == TX_PUBKEYHASH && vSolutions.size() > 0) {
                        uint160 pubKeyHash = uint160(vSolutions[0]);
                        if (isBlacklisted(pubKeyHash, chainparams, pindex->nHeight)) {
                            return state.Invalid(false, REJECT_INVALID, "bad-blacklisted-address",
                                                "Block has a TX input from blacklisted address");
                        }
                    }
                }
            }

            // Check that transaction is BIP68 final
            // BIP68 lock checks (as opposed to nLockTime checks) must
            // be in ConnectBlock because they require the UTXO set
            prevheights.resize(tx.vin.size());
            for (size_t j = 0; j < tx.vin.size(); j++) {
                prevheights[j] = view.AccessCoins(tx.vin[j].prevout.hash)->nHeight;
            }

            if (!SequenceLocks(tx, nLockTimeFlags, &prevheights, *pindex)) {
                return state.DoS(100, error("%s: contains a non-BIP68-final transaction", __func__),
                                 REJECT_INVALID, "bad-txns-nonfinal");
            }
        }

        // GetTransactionSigOpCost counts 3 types of sigops:
        // * legacy (always)
        // * p2sh (when P2SH enabled in flags and excludes coinbase)
        // * witness (when witness enabled in flags and excludes coinbase)
        nSigOpsCost += GetTransactionSigOpCost(tx, view, flags);
        if (nSigOpsCost > MAX_BLOCK_SIGOPS_COST)
            return state.DoS(100, error("ConnectBlock(): too many sigops"),
                             REJECT_INVALID, "bad-blk-sigops");

        txdata.emplace_back(tx);
        if (!tx.IsCoinBase())
        {
            nFees += view.GetValueIn(tx)-tx.GetValueOut();

            std::vector<CScriptCheck> vChecks;
            bool fCacheResults = fJustCheck; /* Don't cache results if we're actually connecting blocks (still consult the cache, though) */
            if (!CheckInputs(chainSigVersion, tx, state, view, fScriptChecks, flags, fCacheResults, txdata[i], nScriptCheckThreads ? &vChecks : NULL))
                return error("ConnectBlock(): CheckInputs on %s failed with %s",
                    tx.GetHash().ToString(), FormatStateMessage(state));
            control.Add(vChecks);
        }

        CTxUndo undoDummy;
        if (i > 0) {
            blockundo.vtxundo.push_back(CTxUndo());
        }
        UpdateCoins(tx, view, i == 0 ? undoDummy : blockundo.vtxundo.back(), pindex->nHeight);

        vPos.push_back(std::make_pair(tx.GetHash(), pos));
        pos.nTxOffset += ::GetSerializeSize(tx, SER_DISK, CLIENT_VERSION);
    }
    int64_t nTime3 = GetTimeMicros(); nTimeConnect += nTime3 - nTime2;
    LogPrint("bench", "      - Connect %u transactions: %.2fms (%.3fms/tx, %.3fms/txin) [%.2fs]\n", (unsigned)block.vtx.size(), 0.001 * (nTime3 - nTime2), 0.001 * (nTime3 - nTime2) / block.vtx.size(), nInputs <= 1 ? 0 : 0.001 * (nTime3 - nTime2) / (nInputs-1), nTimeConnect * 0.000001);

    CAmount blockReward = nFees + GetLuckycoinBlockSubsidy(pindex->nHeight, chainparams.GetConsensus(pindex->nHeight), hashPrevBlock);
    if (block.vtx[0]->GetValueOut() > blockReward)
        return state.DoS(100,
                         error("ConnectBlock(): coinbase pays too much (actual=%d vs limit=%d)",
                               block.vtx[0]->GetValueOut(), blockReward),
                               REJECT_INVALID, "bad-cb-amount");

    if (!control.Wait())
        return state.DoS(100, false);
    int64_t nTime4 = GetTimeMicros(); nTimeVerify += nTime4 - nTime2;
    LogPrint("bench", "    - Verify %u txins: %.2fms (%.3fms/txin) [%.2fs]\n", nInputs - 1, 0.001 * (nTime4 - nTime2), nInputs <= 1 ? 0 : 0.001 * (nTime4 - nTime2) / (nInputs-1), nTimeVerify * 0.000001);

    if (fJustCheck)
        return true;

    // Write undo information to disk
    if (pindex->GetUndoPos().IsNull() || !pindex->IsValid(BLOCK_VALID_SCRIPTS))
    {
        if (pindex->GetUndoPos().IsNull()) {
            CDiskBlockPos _pos;
            if (!FindUndoPos(state, pindex->nFile, _pos, ::GetSerializeSize(blockundo, SER_DISK, CLIENT_VERSION) + 40))
                return error("ConnectBlock(): FindUndoPos failed");
            if (!UndoWriteToDisk(blockundo, _pos, pindex->pprev->GetBlockHash(), chainparams.MessageStart()))
                return AbortNode(state, "Failed to write undo data");

            // update nUndoPos in block index
            pindex->nUndoPos = _pos.nPos;
            pindex->nStatus |= BLOCK_HAVE_UNDO;
        }

        pindex->RaiseValidity(BLOCK_VALID_SCRIPTS);
        setDirtyBlockIndex.insert(pindex);
    }

    if (fTxIndex)
        if (!pblocktree->WriteTxIndex(vPos))
            return AbortNode(state, "Failed to write transaction index");

    // add this block to the view's block chain
    view.SetBestBlock(pindex->GetBlockHash());

    int64_t nTime5 = GetTimeMicros(); nTimeIndex += nTime5 - nTime4;
    LogPrint("bench", "    - Index writing: %.2fms [%.2fs]\n", 0.001 * (nTime5 - nTime4), nTimeIndex * 0.000001);

    // Watch for changes to the previous coinbase transaction.
    static uint256 hashPrevBestCoinBase;
    GetMainSignals().UpdatedTransaction(hashPrevBestCoinBase);
    hashPrevBestCoinBase = block.vtx[0]->GetHash();


    int64_t nTime6 = GetTimeMicros(); nTimeCallbacks += nTime6 - nTime5;
    LogPrint("bench", "    - Callbacks: %.2fms [%.2fs]\n", 0.001 * (nTime6 - nTime5), nTimeCallbacks * 0.000001);

    return true;
}

/**
 * Update the on-disk chain state.
 * The caches and indexes are flushed depending on the mode we're called with
 * if they're too large, if it's been a while since the last write,
 * or always and in all cases if we're in prune mode and are deleting files.
 */
bool static FlushStateToDisk(CValidationState &state, FlushStateMode mode, int nManualPruneHeight) {
    int64_t nMempoolUsage = mempool.DynamicMemoryUsage();
    const CChainParams& chainparams = Params();
    LOCK2(cs_main, cs_LastBlockFile);
    static int64_t nLastWrite = 0;
    static int64_t nLastFlush = 0;
    static int64_t nLastSetChain = 0;
    std::set<int> setFilesToPrune;
    bool fFlushForPrune = false;
    try {
    if (fPruneMode && (fCheckForPruning || nManualPruneHeight > 0) && !fReindex) {
        if (nManualPruneHeight > 0) {
            FindFilesToPruneManual(setFilesToPrune, nManualPruneHeight);
        } else {
            FindFilesToPrune(setFilesToPrune, chainparams.PruneAfterHeight());
            fCheckForPruning = false;
        }
        if (!setFilesToPrune.empty()) {
            fFlushForPrune = true;
            if (!fHavePruned) {
                pblocktree->WriteFlag("prunedblockfiles", true);
                fHavePruned = true;
            }
        }
    }
    int64_t nNow = GetTimeMicros();
    // Avoid writing/flushing immediately after startup.
    if (nLastWrite == 0) {
        nLastWrite = nNow;
    }
    if (nLastFlush == 0) {
        nLastFlush = nNow;
    }
    if (nLastSetChain == 0) {
        nLastSetChain = nNow;
    }
    int64_t nMempoolSizeMax = GetArg("-maxmempool", DEFAULT_MAX_MEMPOOL_SIZE) * 1000000;
    int64_t cacheSize = pcoinsTip->DynamicMemoryUsage() * DB_PEAK_USAGE_FACTOR;
    int64_t nTotalSpace = nCoinCacheUsage + std::max<int64_t>(nMempoolSizeMax - nMempoolUsage, 0);
    // The cache is large and we're within 10% and 200 MiB or 50% and 50MiB of the limit, but we have time now (not in the middle of a block processing).
    bool fCacheLarge = mode == FLUSH_STATE_PERIODIC && cacheSize > std::min(std::max(nTotalSpace / 2, nTotalSpace - MIN_BLOCK_COINSDB_USAGE * 1024 * 1024),
                                                                            std::max((9 * nTotalSpace) / 10, nTotalSpace - MAX_BLOCK_COINSDB_USAGE * 1024 * 1024));
    // The cache is over the limit, we have to write now.
    bool fCacheCritical = mode == FLUSH_STATE_IF_NEEDED && cacheSize > nTotalSpace;
    // It's been a while since we wrote the block index to disk. Do this frequently, so we don't need to redownload after a crash.
    bool fPeriodicWrite = mode == FLUSH_STATE_PERIODIC && nNow > nLastWrite + (int64_t)DATABASE_WRITE_INTERVAL * 1000000;
    // It's been very long since we flushed the cache. Do this infrequently, to optimize cache usage.
    bool fPeriodicFlush = mode == FLUSH_STATE_PERIODIC && nNow > nLastFlush + (int64_t)DATABASE_FLUSH_INTERVAL * 1000000;
    // Combine all conditions that result in a full cache flush.
    bool fDoFullFlush = (mode == FLUSH_STATE_ALWAYS) || fCacheLarge || fCacheCritical || fPeriodicFlush || fFlushForPrune;
    // Write blocks and block index to disk.
    if (fDoFullFlush || fPeriodicWrite) {
        // Depend on nMinDiskSpace to ensure we can write block index
        if (!CheckDiskSpace(0))
            return state.Error("out of disk space");
        // First make sure all block and undo data is flushed to disk.
        FlushBlockFile();
        // Then update all block file information (which may refer to block and undo files).
        {
            std::vector<std::pair<int, const CBlockFileInfo*> > vFiles;
            vFiles.reserve(setDirtyFileInfo.size());
            for (std::set<int>::iterator it = setDirtyFileInfo.begin(); it != setDirtyFileInfo.end(); ) {
                vFiles.push_back(std::make_pair(*it, &vinfoBlockFile[*it]));
                setDirtyFileInfo.erase(it++);
            }
            std::vector<const CBlockIndex*> vBlocks;
            vBlocks.reserve(setDirtyBlockIndex.size());
            for (std::set<CBlockIndex*>::iterator it = setDirtyBlockIndex.begin(); it != setDirtyBlockIndex.end(); ) {
                vBlocks.push_back(*it);
                setDirtyBlockIndex.erase(it++);
            }
            if (!pblocktree->WriteBatchSync(vFiles, nLastBlockFile, vBlocks)) {
                return AbortNode(state, "Failed to write to block index database");
            }
        }
        // Finally remove any pruned files
        if (fFlushForPrune)
            UnlinkPrunedFiles(setFilesToPrune);
        nLastWrite = nNow;
    }
    // Flush best chain related state. This can only be done if the blocks / block index write was also done.
    if (fDoFullFlush) {
        // Typical CCoins structures on disk are around 128 bytes in size.
        // Pushing a new one to the database can cause it to be written
        // twice (once in the log, and once in the tables). This is already
        // an overestimation, as most will delete an existing entry or
        // overwrite one. Still, use a conservative safety factor of 2.
        if (!CheckDiskSpace(128 * 2 * 2 * pcoinsTip->GetCacheSize()))
            return state.Error("out of disk space");
        // Flush the chainstate (which may refer to block index entries).
        if (!pcoinsTip->Flush())
            return AbortNode(state, "Failed to write to coin database");
        nLastFlush = nNow;
    }
    if (fDoFullFlush || ((mode == FLUSH_STATE_ALWAYS || mode == FLUSH_STATE_PERIODIC) && nNow > nLastSetChain + (int64_t)DATABASE_WRITE_INTERVAL * 1000000)) {
        // Update best block in wallet (so we can detect restored wallets).
        GetMainSignals().SetBestChain(chainActive.GetLocator());
        nLastSetChain = nNow;
    }
    } catch (const std::runtime_error& e) {
        return AbortNode(state, std::string("System error while flushing: ") + e.what());
    }
    return true;
}

void FlushStateToDisk() {
    CValidationState state;
    FlushStateToDisk(state, FLUSH_STATE_ALWAYS);
}

void PruneAndFlush() {
    CValidationState state;
    fCheckForPruning = true;
    FlushStateToDisk(state, FLUSH_STATE_NONE);
}

/** Update chainActive and related internal data structures. */
void static UpdateTip(CBlockIndex *pindexNew, const CChainParams& chainParams) {
    chainActive.SetTip(pindexNew);

    // New best block
    mempool.AddTransactionsUpdated(1);

    cvBlockChange.notify_all();

    static bool fWarned = false;
    std::vector<std::string> warningMessages;
    if (!IsInitialBlockDownload())
    {
        int nUpgraded = 0;
        const CBlockIndex* pindex = chainActive.Tip();

        // Check the version of the last 100 blocks to see if we need to upgrade:
        for (int i = 0; i < 100 && pindex != NULL; i++)
        {
            int32_t nExpectedVersion = ComputeBlockVersion(pindex->pprev, chainParams.GetConsensus(pindex->nHeight));
            if (pindex->GetBaseVersion() > VERSIONBITS_LAST_OLD_BLOCK_VERSION && (pindex->GetBaseVersion() & ~nExpectedVersion) != 0)
                ++nUpgraded;
            pindex = pindex->pprev;
        }
        if (nUpgraded > 0)
            warningMessages.push_back(strprintf("%d of last 100 blocks have unexpected version", nUpgraded));
        if (nUpgraded > 100/2)
        {
            std::string strWarning = _("Warning: Unknown block versions being mined! It's possible unknown rules are in effect");
            // notify GetWarnings(), called by Qt and the JSON-RPC code to warn the user:
            SetMiscWarning(strWarning);
            if (!fWarned) {
                AlertNotify(strWarning);
                fWarned = true;
            }
        }
    }
    LogPrintf("%s: new best=%s height=%d version=0x%08x log2_work=%.8g tx=%lu date='%s' progress=%f cache=%.1fMiB(%utx)", __func__,
      chainActive.Tip()->GetBlockHash().ToString(), chainActive.Height(), chainActive.Tip()->nVersion,
      log(chainActive.Tip()->nChainWork.getdouble())/log(2.0), (unsigned long)chainActive.Tip()->nChainTx,
      DateTimeStrFormat("%Y-%m-%d %H:%M:%S", chainActive.Tip()->GetBlockTime()),
      GuessVerificationProgress(chainParams.TxData(), chainActive.Tip()), pcoinsTip->DynamicMemoryUsage() * (1.0 / (1<<20)), pcoinsTip->GetCacheSize());
    if (!warningMessages.empty())
        LogPrintf(" warning='%s'", boost::algorithm::join(warningMessages, ", "));
    LogPrintf("\n");

}

/** Disconnect chainActive's tip. You probably want to call mempool.removeForReorg and manually re-limit mempool size after this, with cs_main held. */
bool static DisconnectTip(CValidationState& state, const CChainParams& chainparams, bool fBare = false)
{
    CBlockIndex *pindexDelete = chainActive.Tip();
    assert(pindexDelete);
    // Read block from disk.
    CBlock block;
    if (!ReadBlockFromDisk(block, pindexDelete, chainparams.GetConsensus(chainActive.Height())))
        return AbortNode(state, "Failed to read block");
    // Apply the block atomically to the chain state.
    int64_t nStart = GetTimeMicros();
    {
        CCoinsViewCache view(pcoinsTip);
        if (!DisconnectBlock(block, state, pindexDelete, view))
            return error("DisconnectTip(): DisconnectBlock %s failed", pindexDelete->GetBlockHash().ToString());
        bool flushed = view.Flush();
        assert(flushed);
    }
    LogPrint("bench", "- Disconnect block: %.2fms\n", (GetTimeMicros() - nStart) * 0.001);
    // Write the chain state to disk, if necessary.
    if (!FlushStateToDisk(state, FLUSH_STATE_IF_NEEDED))
        return false;

    if (!fBare) {
        // Resurrect mempool transactions from the disconnected block.
        std::vector<uint256> vHashUpdate;
        for (const auto& it : block.vtx) {
            const CTransaction& tx = *it;
            // ignore validation errors in resurrected transactions
            CValidationState stateDummy;
            if (tx.IsCoinBase() || !AcceptToMemoryPool(mempool, stateDummy, it, false, NULL, NULL, true)) {
                mempool.removeRecursive(tx, MemPoolRemovalReason::REORG);
            } else if (mempool.exists(tx.GetHash())) {
                vHashUpdate.push_back(tx.GetHash());
            }
        }
        // AcceptToMemoryPool/addUnchecked all assume that new mempool entries have
        // no in-mempool children, which is generally not true when adding
        // previously-confirmed transactions back to the mempool.
        // UpdateTransactionsFromBlock finds descendants of any transactions in this
        // block that were added back and cleans up the mempool state.
        mempool.UpdateTransactionsFromBlock(vHashUpdate);
    }

    // Update chainActive and related variables.
    UpdateTip(pindexDelete->pprev, chainparams);
    // Let wallets know transactions went from 1-confirmed to
    // 0-confirmed or conflicted:
    for (const auto& tx : block.vtx) {
        GetMainSignals().SyncTransaction(*tx, pindexDelete->pprev, CMainSignals::SYNC_TRANSACTION_NOT_IN_BLOCK);
    }
    return true;
}

static int64_t nTimeReadFromDisk = 0;
static int64_t nTimeConnectTotal = 0;
static int64_t nTimeFlush = 0;
static int64_t nTimeChainState = 0;
static int64_t nTimePostConnect = 0;

/**
 * Used to track blocks whose transactions were applied to the UTXO state as a
 * part of a single ActivateBestChainStep call.
 */
struct ConnectTrace {
    std::vector<std::pair<CBlockIndex*, std::shared_ptr<const CBlock> > > blocksConnected;
};

/**
 * Connect a new block to chainActive. pblock is either NULL or a pointer to a CBlock
 * corresponding to pindexNew, to bypass loading it again from disk.
 *
 * The block is always added to connectTrace (either after loading from disk or by copying
 * pblock) - if that is not intended, care must be taken to remove the last entry in
 * blocksConnected in case of failure.
 */
bool static ConnectTip(CValidationState& state, const CChainParams& chainparams, CBlockIndex* pindexNew, const std::shared_ptr<const CBlock>& pblock, ConnectTrace& connectTrace)
{
    assert(pindexNew->pprev == chainActive.Tip());
    // Read block from disk.
    int64_t nTime1 = GetTimeMicros();
    if (!pblock) {
        std::shared_ptr<CBlock> pblockNew = std::make_shared<CBlock>();
        connectTrace.blocksConnected.emplace_back(pindexNew, pblockNew);
        if (!ReadBlockFromDisk(*pblockNew, pindexNew, chainparams.GetConsensus(pindexNew->nHeight)))
            return AbortNode(state, "Failed to read block");
    } else {
        connectTrace.blocksConnected.emplace_back(pindexNew, pblock);
    }
    const CBlock& blockConnecting = *connectTrace.blocksConnected.back().second;
    // Apply the block atomically to the chain state.
    int64_t nTime2 = GetTimeMicros(); nTimeReadFromDisk += nTime2 - nTime1;
    int64_t nTime3;
    LogPrint("bench", "  - Load block from disk: %.2fms [%.2fs]\n", (nTime2 - nTime1) * 0.001, nTimeReadFromDisk * 0.000001);
    {
        CCoinsViewCache view(pcoinsTip);
        bool rv = ConnectBlock(blockConnecting, state, pindexNew, view, chainparams);
        GetMainSignals().BlockChecked(blockConnecting, state);
        if (!rv) {
            if (state.IsInvalid())
                InvalidBlockFound(pindexNew, state);
            return error("ConnectTip(): ConnectBlock %s failed", pindexNew->GetBlockHash().ToString());
        }
        nTime3 = GetTimeMicros(); nTimeConnectTotal += nTime3 - nTime2;
        LogPrint("bench", "  - Connect total: %.2fms [%.2fs]\n", (nTime3 - nTime2) * 0.001, nTimeConnectTotal * 0.000001);
        bool flushed = view.Flush();
        assert(flushed);
    }
    int64_t nTime4 = GetTimeMicros(); nTimeFlush += nTime4 - nTime3;
    LogPrint("bench", "  - Flush: %.2fms [%.2fs]\n", (nTime4 - nTime3) * 0.001, nTimeFlush * 0.000001);
    // Write the chain state to disk, if necessary.
    if (!FlushStateToDisk(state, FLUSH_STATE_IF_NEEDED))
        return false;
    int64_t nTime5 = GetTimeMicros(); nTimeChainState += nTime5 - nTime4;
    LogPrint("bench", "  - Writing chainstate: %.2fms [%.2fs]\n", (nTime5 - nTime4) * 0.001, nTimeChainState * 0.000001);
    // Remove conflicting transactions from the mempool.;
    mempool.removeForBlock(blockConnecting.vtx, pindexNew->nHeight);
    // Update chainActive & related variables.
    UpdateTip(pindexNew, chainparams);

    int64_t nTime6 = GetTimeMicros(); nTimePostConnect += nTime6 - nTime5; nTimeTotal += nTime6 - nTime1;
    LogPrint("bench", "  - Connect postprocess: %.2fms [%.2fs]\n", (nTime6 - nTime5) * 0.001, nTimePostConnect * 0.000001);
    LogPrint("bench", "- Connect block: %.2fms [%.2fs]\n", (nTime6 - nTime1) * 0.001, nTimeTotal * 0.000001);
    return true;
}

/**
 * Return the tip of the chain with the most work in it, that isn't
 * known to be invalid (it's however far from certain to be valid).
 */
static CBlockIndex* FindMostWorkChain() {
    do {
        CBlockIndex *pindexNew = NULL;

        // Find the best candidate header.
        {
            std::set<CBlockIndex*, CBlockIndexWorkComparator>::reverse_iterator it = setBlockIndexCandidates.rbegin();
            if (it == setBlockIndexCandidates.rend())
                return NULL;
            pindexNew = *it;
        }

        // Check whether all blocks on the path between the currently active chain and the candidate are valid.
        // Just going until the active chain is an optimization, as we know all blocks in it are valid already.
        CBlockIndex *pindexTest = pindexNew;
        bool fInvalidAncestor = false;
        while (pindexTest && !chainActive.Contains(pindexTest)) {
            assert(pindexTest->nChainTx || pindexTest->nHeight == 0);

            // Pruned nodes may have entries in setBlockIndexCandidates for
            // which block files have been deleted.  Remove those as candidates
            // for the most work chain if we come across them; we can't switch
            // to a chain unless we have all the non-active-chain parent blocks.
            bool fFailedChain = pindexTest->nStatus & BLOCK_FAILED_MASK;
            bool fMissingData = !(pindexTest->nStatus & BLOCK_HAVE_DATA);
            if (fFailedChain || fMissingData) {
                // Candidate chain is not usable (either invalid or missing data)
                if (fFailedChain && (pindexBestInvalid == NULL || pindexNew->nChainWork > pindexBestInvalid->nChainWork))
                    pindexBestInvalid = pindexNew;
                CBlockIndex *pindexFailed = pindexNew;
                // Remove the entire chain from the set.
                while (pindexTest != pindexFailed) {
                    if (fFailedChain) {
                        pindexFailed->nStatus |= BLOCK_FAILED_CHILD;
                    } else if (fMissingData) {
                        // If we're missing data, then add back to mapBlocksUnlinked,
                        // so that if the block arrives in the future we can try adding
                        // to setBlockIndexCandidates again.
                        mapBlocksUnlinked.insert(std::make_pair(pindexFailed->pprev, pindexFailed));
                    }
                    setBlockIndexCandidates.erase(pindexFailed);
                    pindexFailed = pindexFailed->pprev;
                }
                setBlockIndexCandidates.erase(pindexTest);
                fInvalidAncestor = true;
                break;
            }
            pindexTest = pindexTest->pprev;
        }
        if (!fInvalidAncestor)
            return pindexNew;
    } while(true);
}

/** Delete all entries in setBlockIndexCandidates that are worse than the current tip. */
static void PruneBlockIndexCandidates() {
    // Note that we can't delete the current block itself, as we may need to return to it later in case a
    // reorganization to a better block fails.
    std::set<CBlockIndex*, CBlockIndexWorkComparator>::iterator it = setBlockIndexCandidates.begin();
    while (it != setBlockIndexCandidates.end() && setBlockIndexCandidates.value_comp()(*it, chainActive.Tip())) {
        setBlockIndexCandidates.erase(it++);
    }
    // Either the current tip or a successor of it we're working towards is left in setBlockIndexCandidates.
    assert(!setBlockIndexCandidates.empty());
}

/**
 * Try to make some progress towards making pindexMostWork the active block.
 * pblock is either NULL or a pointer to a CBlock corresponding to pindexMostWork.
 */
static bool ActivateBestChainStep(CValidationState& state, const CChainParams& chainparams, CBlockIndex* pindexMostWork, const std::shared_ptr<const CBlock>& pblock, bool& fInvalidFound, ConnectTrace& connectTrace)
{
    AssertLockHeld(cs_main);
    const CBlockIndex *pindexOldTip = chainActive.Tip();
    const CBlockIndex *pindexFork = chainActive.FindFork(pindexMostWork);

    // Disconnect active blocks which are no longer in the best chain.
    bool fBlocksDisconnected = false;
    while (chainActive.Tip() && chainActive.Tip() != pindexFork) {
        if (!DisconnectTip(state, chainparams))
            return false;
        fBlocksDisconnected = true;
    }

    // Build list of new blocks to connect.
    std::vector<CBlockIndex*> vpindexToConnect;
    bool fContinue = true;
    int nHeight = pindexFork ? pindexFork->nHeight : -1;
    while (fContinue && nHeight != pindexMostWork->nHeight) {
        // Don't iterate the entire list of potential improvements toward the best tip, as we likely only need
        // a few blocks along the way.
        int nTargetHeight = std::min(nHeight + 32, pindexMostWork->nHeight);
        vpindexToConnect.clear();
        vpindexToConnect.reserve(nTargetHeight - nHeight);
        CBlockIndex *pindexIter = pindexMostWork->GetAncestor(nTargetHeight);
        while (pindexIter && pindexIter->nHeight != nHeight) {
            vpindexToConnect.push_back(pindexIter);
            pindexIter = pindexIter->pprev;
        }
        nHeight = nTargetHeight;

        // Connect new blocks.
        BOOST_REVERSE_FOREACH(CBlockIndex *pindexConnect, vpindexToConnect) {
            if (!ConnectTip(state, chainparams, pindexConnect, pindexConnect == pindexMostWork ? pblock : std::shared_ptr<const CBlock>(), connectTrace)) {
                if (state.IsInvalid()) {
                    // The block violates a consensus rule.
                    if (!state.CorruptionPossible())
                        InvalidChainFound(vpindexToConnect.back());
                    state = CValidationState();
                    fInvalidFound = true;
                    fContinue = false;
                    // If we didn't actually connect the block, don't notify listeners about it
                    connectTrace.blocksConnected.pop_back();
                    break;
                } else {
                    // A system error occurred (disk space, database error, ...).
                    return false;
                }
            } else {
                PruneBlockIndexCandidates();
                if (!pindexOldTip || chainActive.Tip()->nChainWork > pindexOldTip->nChainWork) {
                    // We're in a better position than we were. Return temporarily to release the lock.
                    fContinue = false;
                    break;
                }
            }
        }
    }

    if (fBlocksDisconnected) {
        mempool.removeForReorg(pcoinsTip, chainActive.Height() + 1, STANDARD_LOCKTIME_VERIFY_FLAGS);
        LimitMempoolSize(mempool, GetArg("-maxmempool", DEFAULT_MAX_MEMPOOL_SIZE) * 1000000, GetArg("-mempoolexpiry", DEFAULT_MEMPOOL_EXPIRY) * 60 * 60);
    }
    mempool.check(pcoinsTip);

    // Callbacks/notifications for a new best chain.
    if (fInvalidFound)
        CheckForkWarningConditionsOnNewFork(vpindexToConnect.back());
    else
        CheckForkWarningConditions();

    return true;
}

static void NotifyHeaderTip() {
    bool fNotify = false;
    bool fInitialBlockDownload = false;
    static CBlockIndex* pindexHeaderOld = NULL;
    CBlockIndex* pindexHeader = NULL;
    {
        LOCK(cs_main);
        pindexHeader = pindexBestHeader;

        if (pindexHeader != pindexHeaderOld) {
            fNotify = true;
            fInitialBlockDownload = IsInitialBlockDownload();
            pindexHeaderOld = pindexHeader;
        }
    }
    // Send block tip changed notifications without cs_main
    if (fNotify) {
        uiInterface.NotifyHeaderTip(fInitialBlockDownload, pindexHeader);
    }
}

/**
 * Make the best chain active, in multiple steps. The result is either failure
 * or an activated best chain. pblock is either NULL or a pointer to a block
 * that is already loaded (to avoid loading it again from disk).
 */
bool ActivateBestChain(CValidationState &state, const CChainParams& chainparams, std::shared_ptr<const CBlock> pblock) {
    // Note that while we're often called here from ProcessNewBlock, this is
    // far from a guarantee. Things in the P2P/RPC will often end up calling
    // us in the middle of ProcessNewBlock - do not assume pblock is set
    // sanely for performance or correctness!

    CBlockIndex *pindexMostWork = NULL;
    CBlockIndex *pindexNewTip = NULL;
    do {

        const CBlockIndex *pindexFork;
        ConnectTrace connectTrace;
        bool fInitialDownload;
        {
            LOCK(cs_main);
            { // TODO: Tempoarily ensure that mempool removals are notified before
              // connected transactions.  This shouldn't matter, but the abandoned
              // state of transactions in our wallet is currently cleared when we
              // receive another notification and there is a race condition where
              // notification of a connected conflict might cause an outside process
              // to abandon a transaction and then have it inadvertently cleared by
              // the notification that the conflicted transaction was evicted.
            MemPoolConflictRemovalTracker mrt(mempool);
            CBlockIndex *pindexOldTip = chainActive.Tip();
            if (pindexMostWork == NULL) {
                pindexMostWork = FindMostWorkChain();
            }

            // Whether we have anything to do at all.
            if (pindexMostWork == NULL || pindexMostWork == chainActive.Tip())
                return true;

            bool fInvalidFound = false;
            std::shared_ptr<const CBlock> nullBlockPtr;
            if (!ActivateBestChainStep(state, chainparams, pindexMostWork, pblock && pblock->GetHash() == pindexMostWork->GetBlockHash() ? pblock : nullBlockPtr, fInvalidFound, connectTrace))
                return false;

            if (fInvalidFound) {
                // Wipe cache, we may need another branch now.
                pindexMostWork = NULL;
            }
            pindexNewTip = chainActive.Tip();
            pindexFork = chainActive.FindFork(pindexOldTip);
            fInitialDownload = IsInitialBlockDownload();

            // throw all transactions though the signal-interface

            } // MemPoolConflictRemovalTracker destroyed and conflict evictions are notified

            // Transactions in the connnected block are notified
            for (const auto& pair : connectTrace.blocksConnected) {
                assert(pair.second);
                const CBlock& block = *(pair.second);
                for (unsigned int i = 0; i < block.vtx.size(); i++)
                    GetMainSignals().SyncTransaction(*block.vtx[i], pair.first, i);
            }
        }
        // When we reach this point, we switched to a new tip (stored in pindexNewTip).

        // Notifications/callbacks that can run without cs_main

        // Notify external listeners about the new tip.
        GetMainSignals().UpdatedBlockTip(pindexNewTip, pindexFork, fInitialDownload);

        // Always notify the UI if a new block tip was connected
        if (pindexFork != pindexNewTip) {
            uiInterface.NotifyBlockTip(fInitialDownload, pindexNewTip);
        }

        // Perform the shutdown detection to the end of the loop to prevent
        // pindexNewTip being nil
        boost::this_thread::interruption_point();
        if (ShutdownRequested()) {
            LogPrintf("ActivateBestChain: shutdown requested, breaking loop\n");
            break;
        }

    } while (pindexNewTip != pindexMostWork);
    if (pindexNewTip != NULL) {
        CheckBlockIndex(chainparams.GetConsensus(pindexNewTip->nHeight));
    } else {
        CheckBlockIndex(chainparams.GetConsensus(0));
    }

    // Write changes periodically to disk, after relay.
    if (!FlushStateToDisk(state, FLUSH_STATE_PERIODIC)) {
        return false;
    }

    return true;
}


bool PreciousBlock(CValidationState& state, const CChainParams& params, CBlockIndex *pindex)
{
    {
        LOCK(cs_main);
        if (pindex->nChainWork < chainActive.Tip()->nChainWork) {
            // Nothing to do, this block is not at the tip.
            return true;
        }
        if (chainActive.Tip()->nChainWork > nLastPreciousChainwork) {
            // The chain has been extended since the last call, reset the counter.
            nBlockReverseSequenceId = -1;
        }
        nLastPreciousChainwork = chainActive.Tip()->nChainWork;
        setBlockIndexCandidates.erase(pindex);
        pindex->nSequenceId = nBlockReverseSequenceId;
        if (nBlockReverseSequenceId > std::numeric_limits<int32_t>::min()) {
            // We can't keep reducing the counter if somebody really wants to
            // call preciousblock 2**31-1 times on the same set of tips...
            nBlockReverseSequenceId--;
        }
        if (pindex->IsValid(BLOCK_VALID_TRANSACTIONS) && pindex->nChainTx) {
            setBlockIndexCandidates.insert(pindex);
            PruneBlockIndexCandidates();
        }
    }

    return ActivateBestChain(state, params);
}

bool InvalidateBlock(CValidationState& state, const CChainParams& chainparams, CBlockIndex *pindex)
{
    AssertLockHeld(cs_main);

    // We first disconnect backwards and then mark the blocks as invalid.
    // This prevents a case where pruned nodes may fail to invalidateblock
    // and be left unable to start as they have no tip candidates (as there
    // are no blocks that meet the "have data and are not invalid per
    // nStatus" criteria for inclusion in setBlockIndexCandidates).

    bool findexWasInChain = false;
    CBlockIndex *invalidWalkTip = chainActive.Tip();

    while (chainActive.Contains(pindex)) {
        findexWasInChain = true;
        // ActivateBestChain considers blocks already in chainActive
        // unconditionally valid already, so force disconnect away from it.
        if (!DisconnectTip(state, chainparams)) {
            mempool.removeForReorg(pcoinsTip, chainActive.Height() + 1, STANDARD_LOCKTIME_VERIFY_FLAGS);
            return false;
        }
    }

    // Debug print the invalid parent's hash, later list the child hashes.
    LogPrintf("Invalid Block %s.", pindex->GetBlockHash().ToString() );

    // Now mark the blocks we just disconnected as descendants invalid
    // Note: this may not be all descendants, e.g. the disconnected block
    // may be the root of competing block chains that have not settled into
    // one single block chain yet.
    while (findexWasInChain && invalidWalkTip != pindex) {
        LogPrintf("  Invalid Child Block %s.", invalidWalkTip->GetBlockHash().ToString() );
        invalidWalkTip->nStatus |= BLOCK_FAILED_CHILD;
        setDirtyBlockIndex.insert(invalidWalkTip);
        setBlockIndexCandidates.erase(invalidWalkTip);
        invalidWalkTip = invalidWalkTip->pprev;
    }

    // Mark the block itself as invalid.
    pindex->nStatus |= BLOCK_FAILED_VALID;
    setDirtyBlockIndex.insert(pindex);
    setBlockIndexCandidates.erase(pindex);
    gFailedBlocks.insert(pindex);

    LimitMempoolSize(mempool, GetArg("-maxmempool", DEFAULT_MAX_MEMPOOL_SIZE) * 1000000, GetArg("-mempoolexpiry", DEFAULT_MEMPOOL_EXPIRY) * 60 * 60);

    // The resulting new best tip may not be in setBlockIndexCandidates anymore, so
    // add it again.
    BlockMap::iterator it = mapBlockIndex.begin();
    while (it != mapBlockIndex.end()) {
        if (it->second->IsValid(BLOCK_VALID_TRANSACTIONS) && it->second->nChainTx && !setBlockIndexCandidates.value_comp()(it->second, chainActive.Tip())) {
            setBlockIndexCandidates.insert(it->second);
            gFailedBlocks.erase(it->second);
        }
        it++;
    }

    InvalidChainFound(pindex);
    mempool.removeForReorg(pcoinsTip, chainActive.Height() + 1, STANDARD_LOCKTIME_VERIFY_FLAGS);
    uiInterface.NotifyBlockTip(IsInitialBlockDownload(), pindex->pprev);
    return true;
}

bool ResetBlockFailureFlags(CBlockIndex *pindex) {
    AssertLockHeld(cs_main);

    int nHeight = pindex->nHeight;

    // Remove the invalidity flag from this block and all its descendants.
    BlockMap::iterator it = mapBlockIndex.begin();
    while (it != mapBlockIndex.end()) {
        if (!it->second->IsValid() && it->second->GetAncestor(nHeight) == pindex) {
            it->second->nStatus &= ~BLOCK_FAILED_MASK;
            setDirtyBlockIndex.insert(it->second);
            if (it->second->IsValid(BLOCK_VALID_TRANSACTIONS) && it->second->nChainTx && setBlockIndexCandidates.value_comp()(chainActive.Tip(), it->second)) {
                setBlockIndexCandidates.insert(it->second);
            }
            if (it->second == pindexBestInvalid) {
                // Reset invalid block marker if it was pointing to one of those.
                pindexBestInvalid = NULL;
            }
        }
        it++;
    }

    // Remove the invalidity flag from all ancestors too.
    while (pindex != NULL) {
        if (pindex->nStatus & BLOCK_FAILED_MASK) {
            pindex->nStatus &= ~BLOCK_FAILED_MASK;
            setDirtyBlockIndex.insert(pindex);
        }
        pindex = pindex->pprev;
    }
    return true;
}

CBlockIndex* AddToBlockIndex(const CBlockHeader& block)
{
    // Check for duplicate
    uint256 hash = block.GetHash();
    BlockMap::iterator it = mapBlockIndex.find(hash);
    if (it != mapBlockIndex.end())
        return it->second;

    // Construct new block index object
    CBlockIndex* pindexNew = new CBlockIndex(block);
    assert(pindexNew);
    // We assign the sequence id to blocks only when the full data is available,
    // to avoid miners withholding blocks but broadcasting headers, to get a
    // competitive advantage.
    pindexNew->nSequenceId = 0;
    BlockMap::iterator mi = mapBlockIndex.insert(std::make_pair(hash, pindexNew)).first;
    pindexNew->phashBlock = &((*mi).first);
    BlockMap::iterator miPrev = mapBlockIndex.find(block.hashPrevBlock);
    if (miPrev != mapBlockIndex.end())
    {
        pindexNew->pprev = (*miPrev).second;
        pindexNew->nHeight = pindexNew->pprev->nHeight + 1;
        pindexNew->BuildSkip();
    }
    pindexNew->nTimeMax = (pindexNew->pprev ? std::max(pindexNew->pprev->nTimeMax, pindexNew->nTime) : pindexNew->nTime);
    pindexNew->nChainWork = (pindexNew->pprev ? pindexNew->pprev->nChainWork : 0) + GetBlockProof(*pindexNew);
    pindexNew->RaiseValidity(BLOCK_VALID_TREE);
    if (pindexBestHeader == NULL || pindexBestHeader->nChainWork < pindexNew->nChainWork)
        pindexBestHeader = pindexNew;

    setDirtyBlockIndex.insert(pindexNew);

    return pindexNew;
}

/** Mark a block as having its data received and checked (up to BLOCK_VALID_TRANSACTIONS). */
bool ReceivedBlockTransactions(const CBlock &block, CValidationState& state, CBlockIndex *pindexNew, const CDiskBlockPos& pos)
{
    pindexNew->nTx = block.vtx.size();
    pindexNew->nChainTx = 0;
    pindexNew->nFile = pos.nFile;
    pindexNew->nDataPos = pos.nPos;
    pindexNew->nUndoPos = 0;
    pindexNew->nStatus |= BLOCK_HAVE_DATA;
    if (IsWitnessEnabled(pindexNew->pprev, Params().GetConsensus(pindexNew->nHeight))) {
        pindexNew->nStatus |= BLOCK_OPT_WITNESS;
    }
    pindexNew->RaiseValidity(BLOCK_VALID_TRANSACTIONS);
    setDirtyBlockIndex.insert(pindexNew);

    if (pindexNew->pprev == NULL || pindexNew->pprev->nChainTx) {
        // If pindexNew is the genesis block or all parents are BLOCK_VALID_TRANSACTIONS.
        std::deque<CBlockIndex*> queue;
        queue.push_back(pindexNew);

        // Recursively process any descendant blocks that now may be eligible to be connected.
        while (!queue.empty()) {
            CBlockIndex *pindex = queue.front();
            queue.pop_front();
            pindex->nChainTx = (pindex->pprev ? pindex->pprev->nChainTx : 0) + pindex->nTx;
            {
                LOCK(cs_nBlockSequenceId);
                pindex->nSequenceId = nBlockSequenceId++;
            }
            if (chainActive.Tip() == NULL || !setBlockIndexCandidates.value_comp()(pindex, chainActive.Tip())) {
                setBlockIndexCandidates.insert(pindex);
            }
            std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> range = mapBlocksUnlinked.equal_range(pindex);
            while (range.first != range.second) {
                std::multimap<CBlockIndex*, CBlockIndex*>::iterator it = range.first;
                queue.push_back(it->second);
                range.first++;
                mapBlocksUnlinked.erase(it);
            }
        }
    } else {
        if (pindexNew->pprev && pindexNew->pprev->IsValid(BLOCK_VALID_TREE)) {
            mapBlocksUnlinked.insert(std::make_pair(pindexNew->pprev, pindexNew));
        }
    }

    return true;
}

bool FindBlockPos(CValidationState &state, CDiskBlockPos &pos, unsigned int nAddSize, unsigned int nHeight, uint64_t nTime, bool fKnown = false)
{
    LOCK(cs_LastBlockFile);

    unsigned int nFile = fKnown ? pos.nFile : nLastBlockFile;
    if (vinfoBlockFile.size() <= nFile) {
        vinfoBlockFile.resize(nFile + 1);
    }

    if (!fKnown) {
        while (vinfoBlockFile[nFile].nSize + nAddSize >= MAX_BLOCKFILE_SIZE) {
            nFile++;
            if (vinfoBlockFile.size() <= nFile) {
                vinfoBlockFile.resize(nFile + 1);
            }
        }
        pos.nFile = nFile;
        pos.nPos = vinfoBlockFile[nFile].nSize;
    }

    if ((int)nFile != nLastBlockFile) {
        if (!fKnown) {
            LogPrintf("Leaving block file %i: %s\n", nLastBlockFile, vinfoBlockFile[nLastBlockFile].ToString());
        }
        FlushBlockFile(!fKnown);
        nLastBlockFile = nFile;
    }

    vinfoBlockFile[nFile].AddBlock(nHeight, nTime);
    if (fKnown)
        vinfoBlockFile[nFile].nSize = std::max(pos.nPos + nAddSize, vinfoBlockFile[nFile].nSize);
    else
        vinfoBlockFile[nFile].nSize += nAddSize;

    if (!fKnown) {
        unsigned int nOldChunks = (pos.nPos + BLOCKFILE_CHUNK_SIZE - 1) / BLOCKFILE_CHUNK_SIZE;
        unsigned int nNewChunks = (vinfoBlockFile[nFile].nSize + BLOCKFILE_CHUNK_SIZE - 1) / BLOCKFILE_CHUNK_SIZE;
        if (nNewChunks > nOldChunks) {
            if (fPruneMode)
                fCheckForPruning = true;
            if (CheckDiskSpace(nNewChunks * BLOCKFILE_CHUNK_SIZE - pos.nPos)) {
                FILE *file = OpenBlockFile(pos);
                if (file) {
                    LogPrintf("Pre-allocating up to position 0x%x in blk%05u.dat\n", nNewChunks * BLOCKFILE_CHUNK_SIZE, pos.nFile);
                    AllocateFileRange(file, pos.nPos, nNewChunks * BLOCKFILE_CHUNK_SIZE - pos.nPos);
                    fclose(file);
                }
            }
            else
                return state.Error("out of disk space");
        }
    }

    setDirtyFileInfo.insert(nFile);
    return true;
}

bool FindUndoPos(CValidationState &state, int nFile, CDiskBlockPos &pos, unsigned int nAddSize)
{
    pos.nFile = nFile;

    LOCK(cs_LastBlockFile);

    unsigned int nNewSize;
    pos.nPos = vinfoBlockFile[nFile].nUndoSize;
    nNewSize = vinfoBlockFile[nFile].nUndoSize += nAddSize;
    setDirtyFileInfo.insert(nFile);

    unsigned int nOldChunks = (pos.nPos + UNDOFILE_CHUNK_SIZE - 1) / UNDOFILE_CHUNK_SIZE;
    unsigned int nNewChunks = (nNewSize + UNDOFILE_CHUNK_SIZE - 1) / UNDOFILE_CHUNK_SIZE;
    if (nNewChunks > nOldChunks) {
        if (fPruneMode)
            fCheckForPruning = true;
        if (CheckDiskSpace(nNewChunks * UNDOFILE_CHUNK_SIZE - pos.nPos)) {
            FILE *file = OpenUndoFile(pos);
            if (file) {
                LogPrintf("Pre-allocating up to position 0x%x in rev%05u.dat\n", nNewChunks * UNDOFILE_CHUNK_SIZE, pos.nFile);
                AllocateFileRange(file, pos.nPos, nNewChunks * UNDOFILE_CHUNK_SIZE - pos.nPos);
                fclose(file);
            }
        }
        else
            return state.Error("out of disk space");
    }

    return true;
}

bool CheckBlockHeader(const CBlockHeader& block, CValidationState& state, bool fCheckPOW)
{
    // Check proof of work matches claimed amount
    // We don't have block height as this is called without context (i.e. without
    // knowing the previous block), but that's okay, as the checks done are permissive
    // (i.e. doesn't check work limit or whether AuxPoW is enabled)
    if (fCheckPOW && !CheckAuxPowProofOfWork(block, Params().GetConsensus(0)))
        return state.DoS(50, false, REJECT_INVALID, "high-hash", false, "proof of work failed");

    return true;
}

bool CheckBlock(const CBlock& block, CValidationState& state, bool fCheckPOW, bool fCheckMerkleRoot)
{
    // These are checks that are independent of context.

    if (block.fChecked)
        return true;

    // Check that the header is valid (particularly PoW).  This is mostly
    // redundant with the call in AcceptBlockHeader.
    if (!CheckBlockHeader(block, state, fCheckPOW))
        return false;

    // Check the merkle root.
    if (fCheckMerkleRoot) {
        bool mutated;
        uint256 hashMerkleRoot2 = BlockMerkleRoot(block, &mutated);
        if (block.hashMerkleRoot != hashMerkleRoot2)
            return state.DoS(100, false, REJECT_INVALID, "bad-txnmrklroot", true, "hashMerkleRoot mismatch");

        // Check for merkle tree malleability (CVE-2012-2459): repeating sequences
        // of transactions in a block without affecting the merkle root of a block,
        // while still invalidating it.
        if (mutated)
            return state.DoS(100, false, REJECT_INVALID, "bad-txns-duplicate", true, "duplicate transaction");
    }

    // All potential-corruption validation must be done before we do any
    // transaction validation, as otherwise we may mark the header as invalid
    // because we receive the wrong transactions for it.
    // Note that witness malleability is checked in ContextualCheckBlock, so no
    // checks that use witness data may be performed here.

    // Size limits
    if (block.vtx.empty() || block.vtx.size() > MAX_BLOCK_BASE_SIZE || ::GetSerializeSize(block, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS) > MAX_BLOCK_BASE_SIZE)
        return state.DoS(100, false, REJECT_INVALID, "bad-blk-length", false, "size limits failed");

    // First transaction must be coinbase, the rest must not be
    if (block.vtx.empty() || !block.vtx[0]->IsCoinBase())
        return state.DoS(100, false, REJECT_INVALID, "bad-cb-missing", false, "first tx is not coinbase");
    for (unsigned int i = 1; i < block.vtx.size(); i++)
        if (block.vtx[i]->IsCoinBase())
            return state.DoS(100, false, REJECT_INVALID, "bad-cb-multiple", false, "more than one coinbase");

    // Check transactions
    for (const auto& tx : block.vtx)
        if (!CheckTransaction(*tx, state, true))
            return state.Invalid(false, state.GetRejectCode(), state.GetRejectReason(),
                                 strprintf("Transaction check failed (tx hash %s) %s", tx->GetHash().ToString(), state.GetDebugMessage()));

    unsigned int nSigOps = 0;
    for (const auto& tx : block.vtx)
    {
        nSigOps += GetLegacySigOpCount(*tx);
    }
    if (nSigOps * WITNESS_SCALE_FACTOR > MAX_BLOCK_SIGOPS_COST)
        return state.DoS(100, false, REJECT_INVALID, "bad-blk-sigops", false, "out-of-bounds SigOpCount");

    if (fCheckPOW && fCheckMerkleRoot)
        block.fChecked = true;

    return true;
}

static bool CheckIndexAgainstCheckpoint(const CBlockIndex* pindexPrev, CValidationState& state, const CChainParams& chainparams, const uint256& hash)
{
    if (*pindexPrev->phashBlock == chainparams.GetConsensus(0).hashGenesisBlock)
        return true;

    int nHeight = pindexPrev->nHeight+1;
    // Don't accept any forks from the main chain prior to last checkpoint
    CBlockIndex* pcheckpoint = Checkpoints::GetLastCheckpoint(chainparams.Checkpoints());
    if (pcheckpoint && nHeight < pcheckpoint->nHeight)
        return state.DoS(100, error("%s: forked chain older than last checkpoint (height %d)", __func__, nHeight));

    return true;
}

bool IsWitnessEnabled(const CBlockIndex* pindexPrev, const Consensus::Params& params)
{
    LOCK(cs_main);
    return (VersionBitsState(pindexPrev, params, Consensus::DEPLOYMENT_SEGWIT, versionbitscache) == THRESHOLD_ACTIVE);
}

ChainSigVersion GetChainSigVersion(const CBlockIndex* pindexPrev, const Consensus::Params& params)
{
    if (pindexPrev->nHeight >= 276500) {
        return CHAINSIG_VERSION_REVIVAL;
    }

    return CHAINSIG_VERSION_ORIGINAL_UNSAFE_DEPRECATED;
}

// Compute at which vout of the block's coinbase transaction the witness
// commitment occurs, or -1 if not found.
static int GetWitnessCommitmentIndex(const CBlock& block)
{
    int commitpos = -1;
    if (!block.vtx.empty()) {
        for (size_t o = 0; o < block.vtx[0]->vout.size(); o++) {
            if (block.vtx[0]->vout[o].scriptPubKey.size() >= 38 && block.vtx[0]->vout[o].scriptPubKey[0] == OP_RETURN && block.vtx[0]->vout[o].scriptPubKey[1] == 0x24 && block.vtx[0]->vout[o].scriptPubKey[2] == 0xaa && block.vtx[0]->vout[o].scriptPubKey[3] == 0x21 && block.vtx[0]->vout[o].scriptPubKey[4] == 0xa9 && block.vtx[0]->vout[o].scriptPubKey[5] == 0xed) {
                commitpos = o;
            }
        }
    }
    return commitpos;
}

void UpdateUncommittedBlockStructures(CBlock& block, const CBlockIndex* pindexPrev, const Consensus::Params& consensusParams)
{
    int commitpos = GetWitnessCommitmentIndex(block);
    static const std::vector<unsigned char> nonce(32, 0x00);
    if (commitpos != -1 && IsWitnessEnabled(pindexPrev, consensusParams) && !block.vtx[0]->HasWitness()) {
        CMutableTransaction tx(*block.vtx[0]);
        tx.vin[0].scriptWitness.stack.resize(1);
        tx.vin[0].scriptWitness.stack[0] = nonce;
        block.vtx[0] = MakeTransactionRef(std::move(tx));
    }
}

std::vector<unsigned char> GenerateCoinbaseCommitment(CBlock& block, const CBlockIndex* pindexPrev, const Consensus::Params& consensusParams)
{
    std::vector<unsigned char> commitment;
    int commitpos = GetWitnessCommitmentIndex(block);
    std::vector<unsigned char> ret(32, 0x00);
    if (consensusParams.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nTimeout != 0) {
        if (commitpos == -1) {
            uint256 witnessroot = BlockWitnessMerkleRoot(block, NULL);
            CHash256().Write(witnessroot.begin(), 32).Write(&ret[0], 32).Finalize(witnessroot.begin());
            CTxOut out;
            out.nValue = 0;
            out.scriptPubKey.resize(38);
            out.scriptPubKey[0] = OP_RETURN;
            out.scriptPubKey[1] = 0x24;
            out.scriptPubKey[2] = 0xaa;
            out.scriptPubKey[3] = 0x21;
            out.scriptPubKey[4] = 0xa9;
            out.scriptPubKey[5] = 0xed;
            memcpy(&out.scriptPubKey[6], witnessroot.begin(), 32);
            commitment = std::vector<unsigned char>(out.scriptPubKey.begin(), out.scriptPubKey.end());
            CMutableTransaction tx(*block.vtx[0]);
            tx.vout.push_back(out);
            block.vtx[0] = MakeTransactionRef(std::move(tx));
        }
    }
    UpdateUncommittedBlockStructures(block, pindexPrev, consensusParams);
    return commitment;
}

bool ContextualCheckBlockHeader(const CBlockHeader& block, CValidationState& state, const CBlockIndex* pindexPrev, int64_t nAdjustedTime)
{
    const int nHeight = pindexPrev == NULL ? 0 : pindexPrev->nHeight + 1;
    const Consensus::Params& consensusParams = Params().GetConsensus(nHeight);

    // Disallow legacy blocks after merge-mining start.
    if (!consensusParams.fAllowLegacyBlocks
        && block.IsLegacy())
        return state.DoS(100, error("%s : legacy block after auxpow start",
                                    __func__),
                         REJECT_INVALID, "late-legacy-block");

    // Luckycoin: Disallow AuxPow blocks before it is activated.
    // TODO: Remove this test, as checkpoints will enforce this for us now
    // NOTE: Previously this had its own fAllowAuxPoW flag, but that's always the opposite of fAllowLegacyBlocks
    if (consensusParams.fAllowLegacyBlocks
        && block.IsAuxpow())
        return state.DoS(100, error("%s : auxpow blocks are not allowed at height %d, parameters effective from %d",
                                    __func__, pindexPrev->nHeight + 1, consensusParams.nHeightEffective),
                         REJECT_INVALID, "early-auxpow-block");

    // Check proof of work
    if (block.nBits != GetNextWorkRequired(pindexPrev, &block, consensusParams))
        return state.DoS(100, false, REJECT_INVALID, "bad-diffbits", false, "incorrect proof of work");

    // Check timestamp against prev
    if (block.GetBlockTime() <= pindexPrev->GetMedianTimePast())
        return state.Invalid(false, REJECT_INVALID, "time-too-old", "block's timestamp is too early");

    // Check timestamp
    if (block.GetBlockTime() > nAdjustedTime + 2 * 60 * 60)
        return state.Invalid(false, REJECT_INVALID, "time-too-new", "block timestamp too far in the future");

    // Reject outdated version blocks when 95% (75% on testnet) of the network has upgraded:
    // check for version 2, 3 and 4 upgrades
    // Luckycoin: Version 2 enforcement was never used
    if((block.GetBaseVersion() < 3 && nHeight >= consensusParams.BIP66Height) ||
       (block.GetBaseVersion() < 4 && nHeight >= consensusParams.BIP65Height))
            return state.Invalid(false, REJECT_OBSOLETE, strprintf("bad-version(0x%08x)", block.GetBaseVersion()),
                                 strprintf("rejected nVersion=0x%08x block", block.GetBaseVersion()));

    return true;
}

bool ContextualCheckBlock(const CBlock& block, CValidationState& state, const CBlockIndex* pindexPrev)
{
    const int nHeight = pindexPrev == NULL ? 0 : pindexPrev->nHeight + 1;
    const CChainParams& chainParams = Params();
    const Consensus::Params& consensusParams = chainParams.GetConsensus(nHeight);

    // Start enforcing BIP113 (Median Time Past) using versionbits logic.
    // Luckycoin: We probably want to disable this
    int nLockTimeFlags = 0;
    if (VersionBitsState(pindexPrev, consensusParams, Consensus::DEPLOYMENT_CSV, versionbitscache) == THRESHOLD_ACTIVE) {
        nLockTimeFlags |= LOCKTIME_MEDIAN_TIME_PAST;
    }

    int64_t nLockTimeCutoff = (nLockTimeFlags & LOCKTIME_MEDIAN_TIME_PAST)
                              ? pindexPrev->GetMedianTimePast()
                              : block.GetBlockTime();

    // Check that all transactions are finalized
    for (const auto& tx : block.vtx) {
        if (!IsFinalTx(*tx, nHeight, nLockTimeCutoff)) {
            return state.DoS(10, false, REJECT_INVALID, "bad-txns-nonfinal", false, "non-final transaction");
        }
    }

    // Enforce rule that the coinbase starts with serialized block height
    if (nHeight >= consensusParams.BIP34Height)
    {
        CScript expect = CScript() << nHeight;
        if (block.vtx[0]->vin[0].scriptSig.size() < expect.size() ||
            !std::equal(expect.begin(), expect.end(), block.vtx[0]->vin[0].scriptSig.begin())) {
            return state.DoS(100, false, REJECT_INVALID, "bad-cb-height", false, "block height mismatch in coinbase");
        }
    }

    // Validation for witness commitments.
    // * We compute the witness hash (which is the hash including witnesses) of all the block's transactions, except the
    //   coinbase (where 0x0000....0000 is used instead).
    // * The coinbase scriptWitness is a stack of a single 32-byte vector, containing a witness nonce (unconstrained).
    // * We build a merkle tree with all those witness hashes as leaves (similar to the hashMerkleRoot in the block header).
    // * There must be at least one output whose scriptPubKey is a single 36-byte push, the first 4 bytes of which are
    //   {0xaa, 0x21, 0xa9, 0xed}, and the following 32 bytes are SHA256^2(witness root, witness nonce). In case there are
    //   multiple, the last one is used.
    bool fHaveWitness = false;
    if (VersionBitsState(pindexPrev, consensusParams, Consensus::DEPLOYMENT_SEGWIT, versionbitscache) == THRESHOLD_ACTIVE) {
        int commitpos = GetWitnessCommitmentIndex(block);
        if (commitpos != -1) {
            bool malleated = false;
            uint256 hashWitness = BlockWitnessMerkleRoot(block, &malleated);
            // The malleation check is ignored; as the transaction tree itself
            // already does not permit it, it is impossible to trigger in the
            // witness tree.
            if (block.vtx[0]->vin[0].scriptWitness.stack.size() != 1 || block.vtx[0]->vin[0].scriptWitness.stack[0].size() != 32) {
                return state.DoS(100, false, REJECT_INVALID, "bad-witness-nonce-size", true, strprintf("%s : invalid witness nonce size", __func__));
            }
            CHash256().Write(hashWitness.begin(), 32).Write(&block.vtx[0]->vin[0].scriptWitness.stack[0][0], 32).Finalize(hashWitness.begin());
            if (memcmp(hashWitness.begin(), &block.vtx[0]->vout[commitpos].scriptPubKey[6], 32)) {
                return state.DoS(100, false, REJECT_INVALID, "bad-witness-merkle-match", true, strprintf("%s : witness merkle commitment mismatch", __func__));
            }
            fHaveWitness = true;
        }
    }

    // No witness data is allowed in blocks that don't commit to witness data, as this would otherwise leave room for spam
    if (!fHaveWitness) {
        for (size_t i = 0; i < block.vtx.size(); i++) {
            if (block.vtx[i]->HasWitness()) {
                return state.DoS(100, false, REJECT_INVALID, "unexpected-witness", true, strprintf("%s : unexpected witness data found", __func__));
            }
        }
    }

    // After the coinbase witness nonce and commitment are verified,
    // we can check if the block weight passes (before we've checked the
    // coinbase witness, it would be possible for the weight to be too
    // large by filling up the coinbase witness, which doesn't change
    // the block hash, so we couldn't mark the block as permanently
    // failed).
    if (GetBlockWeight(block) > MAX_BLOCK_WEIGHT) {
        return state.DoS(100, false, REJECT_INVALID, "bad-blk-weight", false, strprintf("%s : weight limit failed", __func__));
    }

    return true;
}

static bool AcceptBlockHeader(const CBlockHeader& block, CValidationState& state, const CChainParams& chainparams, CBlockIndex** ppindex)
{
    AssertLockHeld(cs_main);
    // Check for duplicate
    uint256 hash = block.GetHash();
    BlockMap::iterator miSelf = mapBlockIndex.find(hash);
    CBlockIndex *pindex = NULL;
    if (hash != chainparams.GetConsensus(0).hashGenesisBlock) {

        if (miSelf != mapBlockIndex.end()) {
            // Block header is already known.
            pindex = miSelf->second;
            if (ppindex)
                *ppindex = pindex;
            if (pindex->nStatus & BLOCK_FAILED_MASK)
                return state.Invalid(error("%s: block %s is marked invalid", __func__, hash.ToString()), 0, "duplicate");
            return true;
        }

        if (!CheckBlockHeader(block, state))
            return error("%s: Consensus::CheckBlockHeader: %s, %s", __func__, hash.ToString(), FormatStateMessage(state));

        // Get prev block index
        CBlockIndex* pindexPrev = NULL;
        BlockMap::iterator mi = mapBlockIndex.find(block.hashPrevBlock);
        if (mi == mapBlockIndex.end())
            return state.DoS(10, error("%s: prev block not found", __func__), 0, "bad-prevblk");
        pindexPrev = (*mi).second;
        if (pindexPrev->nStatus & BLOCK_FAILED_MASK)
            return state.DoS(100, error("%s: prev block invalid", __func__), REJECT_INVALID, "bad-prevblk");

        assert(pindexPrev);
        if (fCheckpointsEnabled && !CheckIndexAgainstCheckpoint(pindexPrev, state, chainparams, hash))
            return error("%s: CheckIndexAgainstCheckpoint(): %s", __func__, state.GetRejectReason().c_str());

        if (!ContextualCheckBlockHeader(block, state, pindexPrev, GetAdjustedTime()))
            return error("%s: Consensus::ContextualCheckBlockHeader: %s, %s", __func__, hash.ToString(), FormatStateMessage(state));

        if (!pindexPrev->IsValid(BLOCK_VALID_SCRIPTS)) {
            for (const CBlockIndex* failedit : gFailedBlocks) {
                if (pindexPrev->GetAncestor(failedit->nHeight) == failedit) {
                    assert(failedit->nStatus & BLOCK_FAILED_VALID);
                    CBlockIndex* invalidWalk = pindexPrev;
                    while (invalidWalk != failedit) {
                        invalidWalk->nStatus |= BLOCK_FAILED_CHILD;
                        setDirtyBlockIndex.insert(invalidWalk);
                        invalidWalk = invalidWalk->pprev;
                    }

                    LogPrintf( "AcceptBlockHeader(): Invalid block %s, rejected child hash %s.", invalidWalk->GetBlockHash().ToString(), hash.ToString()  );
                    return state.DoS(100, error("%s: prev block invalid", __func__), REJECT_INVALID, "bad-prevblk");
                }
            }
        }
    }
    if (pindex == NULL)
        pindex = AddToBlockIndex(block);

    if (ppindex)
        *ppindex = pindex;

    CheckBlockIndex(chainparams.GetConsensus(pindex->nHeight));

    return true;
}

// Exposed wrapper for AcceptBlockHeader
bool ProcessNewBlockHeaders(const std::vector<CBlockHeader>& headers, CValidationState& state, const CChainParams& chainparams, const CBlockIndex** ppindex)
{
    {
        LOCK(cs_main);
        for (const CBlockHeader& header : headers) {
            CBlockIndex *pindex = NULL; // Use a temp pindex instead of ppindex to avoid a const_cast
            if (!AcceptBlockHeader(header, state, chainparams, &pindex)) {
                return false;
            }
            if (ppindex) {
                *ppindex = pindex;
            }
        }
    }
    NotifyHeaderTip();
    return true;
}

/** Store block on disk. If dbp is non-NULL, the file is known to already reside on disk */
static bool AcceptBlock(const std::shared_ptr<const CBlock>& pblock, CValidationState& state, const CChainParams& chainparams, CBlockIndex** ppindex, bool fRequested, const CDiskBlockPos* dbp, bool* fNewBlock)
{
    const CBlock& block = *pblock;

    if (fNewBlock) *fNewBlock = false;
    AssertLockHeld(cs_main);

    CBlockIndex *pindexDummy = NULL;
    CBlockIndex *&pindex = ppindex ? *ppindex : pindexDummy;

    if (!AcceptBlockHeader(block, state, chainparams, &pindex))
        return false;

    // Try to process all requested blocks that we don't have, but only
    // process an unrequested block if it's new and has enough work to
    // advance our tip, and isn't too many blocks ahead.
    bool fAlreadyHave = pindex->nStatus & BLOCK_HAVE_DATA;
    bool fHasMoreWork = (chainActive.Tip() ? pindex->nChainWork > chainActive.Tip()->nChainWork : true);
    // Blocks that are too out-of-order needlessly limit the effectiveness of
    // pruning, because pruning will not delete block files that contain any
    // blocks which are too close in height to the tip.  Apply this test
    // regardless of whether pruning is enabled; it should generally be safe to
    // not process unrequested blocks.
    bool fTooFarAhead = (pindex->nHeight > int(chainActive.Height() + MIN_BLOCKS_TO_KEEP));

    // TODO: Decouple this function from the block download logic by removing fRequested
    // This requires some new chain datastructure to efficiently look up if a
    // block is in a chain leading to a candidate for best tip, despite not
    // being such a candidate itself.

    // TODO: deal better with return value and error conditions for duplicate
    // and unrequested blocks.
    if (fAlreadyHave) return true;
    if (!fRequested) {  // If we didn't ask for it:
        if (pindex->nTx != 0) return true;  // This is a previously-processed block that was pruned
        if (!fHasMoreWork) return true;     // Don't process less-work chains
        if (fTooFarAhead) return true;      // Block height is too high
    }
    if (fNewBlock) *fNewBlock = true;

    if (!CheckBlock(block, state) ||
        !ContextualCheckBlock(block, state, pindex->pprev)) {
        if (state.IsInvalid() && !state.CorruptionPossible()) {
            pindex->nStatus |= BLOCK_FAILED_VALID;
            setDirtyBlockIndex.insert(pindex);
        }
        return error("%s: %s", __func__, FormatStateMessage(state));
    }

    // Header is valid/has work, merkle tree and segwit merkle tree are good...RELAY NOW
    // (but if it does not build on our best tip, let the SendMessages loop relay it)
    if (!IsInitialBlockDownload() && chainActive.Tip() == pindex->pprev)
        GetMainSignals().NewPoWValidBlock(pindex, pblock);

    int nHeight = pindex->nHeight;

    // Write block to history file
    try {
        unsigned int nBlockSize = ::GetSerializeSize(block, SER_DISK, CLIENT_VERSION);
        CDiskBlockPos blockPos;
        if (dbp != NULL)
            blockPos = *dbp;
        if (!FindBlockPos(state, blockPos, nBlockSize+8, nHeight, block.GetBlockTime(), dbp != NULL))
            return error("AcceptBlock(): FindBlockPos failed");
        if (dbp == NULL)
            if (!WriteBlockToDisk(block, blockPos, chainparams.MessageStart()))
                AbortNode(state, "Failed to write block");
        if (!ReceivedBlockTransactions(block, state, pindex, blockPos))
            return error("AcceptBlock(): ReceivedBlockTransactions failed");
    } catch (const std::runtime_error& e) {
        return AbortNode(state, std::string("System error: ") + e.what());
    }

    if (fCheckForPruning)
        FlushStateToDisk(state, FLUSH_STATE_NONE); // we just allocated more disk space for block files

    return true;
}

static bool IsSuperMajority(int minVersion, const CBlockIndex* pstart, unsigned nRequired, const Consensus::Params& consensusParams)
{
    unsigned int nFound = 0;
    for (int i = 0; i < consensusParams.nMajorityWindow && nFound < nRequired && pstart != NULL; i++)
    {
        if (pstart->GetBaseVersion() >= minVersion)
            ++nFound;
        pstart = pstart->pprev;
    }
    return (nFound >= nRequired);
}

bool ProcessNewBlock(const CChainParams& chainparams, const std::shared_ptr<const CBlock> pblock, bool fForceProcessing, bool *fNewBlock)
{
    {
        CBlockIndex *pindex = NULL;
        if (fNewBlock) *fNewBlock = false;
        CValidationState state;
        // Ensure that CheckBlock() passes before calling AcceptBlock, as
        // belt-and-suspenders.
        bool ret = CheckBlock(*pblock, state);

        LOCK(cs_main);

        if (ret) {
            // Store to disk
            ret = AcceptBlock(pblock, state, chainparams, &pindex, fForceProcessing, NULL, fNewBlock);
        }
        CheckBlockIndex(chainparams.GetConsensus(chainActive.Height()));
        if (!ret) {
            GetMainSignals().BlockChecked(*pblock, state);
            return error("%s: AcceptBlock FAILED", __func__);
        }
    }

    NotifyHeaderTip();

    CValidationState state; // Only used to report errors, not invalidity - ignore it
    if (!ActivateBestChain(state, chainparams, pblock))
        return error("%s: ActivateBestChain failed", __func__);

    return true;
}

bool TestBlockValidity(CValidationState& state, const CChainParams& chainparams, const CBlock& block, CBlockIndex* pindexPrev, bool fCheckPOW, bool fCheckMerkleRoot)
{
    AssertLockHeld(cs_main);
    assert(pindexPrev && pindexPrev == chainActive.Tip());
    if (fCheckpointsEnabled && !CheckIndexAgainstCheckpoint(pindexPrev, state, chainparams, block.GetHash()))
        return error("%s: CheckIndexAgainstCheckpoint(): %s", __func__, state.GetRejectReason().c_str());

    CCoinsViewCache viewNew(pcoinsTip);
    CBlockIndex indexDummy(block);
    indexDummy.pprev = pindexPrev;
    indexDummy.nHeight = pindexPrev->nHeight + 1;

    // NOTE: CheckBlockHeader is called by CheckBlock
    if (!ContextualCheckBlockHeader(block, state, pindexPrev, GetAdjustedTime()))
        return error("%s: Consensus::ContextualCheckBlockHeader: %s", __func__, FormatStateMessage(state));
    if (!CheckBlock(block, state, fCheckPOW, fCheckMerkleRoot))
        return error("%s: Consensus::CheckBlock: %s", __func__, FormatStateMessage(state));
    if (!ContextualCheckBlock(block, state, pindexPrev))
        return error("%s: Consensus::ContextualCheckBlock: %s", __func__, FormatStateMessage(state));
    if (!ConnectBlock(block, state, &indexDummy, viewNew, chainparams, true))
        return false;
    assert(state.IsValid());

    return true;
}

/**
 * BLOCK PRUNING CODE
 */

/* Calculate the amount of disk space the block & undo files currently use */
uint64_t CalculateCurrentUsage()
{
    LOCK(cs_LastBlockFile);

    uint64_t retval = 0;
    BOOST_FOREACH(const CBlockFileInfo &file, vinfoBlockFile) {
        retval += file.nSize + file.nUndoSize;
    }
    return retval;
}

/* Prune a block file (modify associated database entries)*/
void PruneOneBlockFile(const int fileNumber)
{
    LOCK(cs_LastBlockFile);

    for (BlockMap::iterator it = mapBlockIndex.begin(); it != mapBlockIndex.end(); ++it) {
        CBlockIndex* pindex = it->second;
        if (pindex->nFile == fileNumber) {
            pindex->nStatus &= ~BLOCK_HAVE_DATA;
            pindex->nStatus &= ~BLOCK_HAVE_UNDO;
            pindex->nFile = 0;
            pindex->nDataPos = 0;
            pindex->nUndoPos = 0;
            setDirtyBlockIndex.insert(pindex);

            // Prune from mapBlocksUnlinked -- any block we prune would have
            // to be downloaded again in order to consider its chain, at which
            // point it would be considered as a candidate for
            // mapBlocksUnlinked or setBlockIndexCandidates.
            std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> range = mapBlocksUnlinked.equal_range(pindex->pprev);
            while (range.first != range.second) {
                std::multimap<CBlockIndex *, CBlockIndex *>::iterator _it = range.first;
                range.first++;
                if (_it->second == pindex) {
                    mapBlocksUnlinked.erase(_it);
                }
            }
        }
    }

    vinfoBlockFile[fileNumber].SetNull();
    setDirtyFileInfo.insert(fileNumber);
}


void UnlinkPrunedFiles(const std::set<int>& setFilesToPrune)
{
    for (std::set<int>::iterator it = setFilesToPrune.begin(); it != setFilesToPrune.end(); ++it) {
        CDiskBlockPos pos(*it, 0);
        boost::filesystem::remove(GetBlockPosFilename(pos, "blk"));
        boost::filesystem::remove(GetBlockPosFilename(pos, "rev"));
        LogPrintf("Prune: %s deleted blk/rev (%05u)\n", __func__, *it);
    }
}

/* Calculate the block/rev files to delete based on height specified by user with RPC command pruneblockchain */
void FindFilesToPruneManual(std::set<int>& setFilesToPrune, int nManualPruneHeight)
{
    assert(fPruneMode && nManualPruneHeight > 0);

    LOCK2(cs_main, cs_LastBlockFile);
    if (chainActive.Tip() == NULL)
        return;

    // last block to prune is the lesser of (user-specified height, MIN_BLOCKS_TO_KEEP from the tip)
    unsigned int nLastBlockWeCanPrune = std::min((unsigned)nManualPruneHeight, chainActive.Height() - MIN_BLOCKS_TO_KEEP);
    int count=0;
    for (int fileNumber = 0; fileNumber < nLastBlockFile; fileNumber++) {
        if (vinfoBlockFile[fileNumber].nSize == 0 || vinfoBlockFile[fileNumber].nHeightLast > nLastBlockWeCanPrune)
            continue;
        PruneOneBlockFile(fileNumber);
        setFilesToPrune.insert(fileNumber);
        count++;
    }
    LogPrintf("Prune (Manual): prune_height=%d removed %d blk/rev pairs\n", nLastBlockWeCanPrune, count);
}

/* This function is called from the RPC code for pruneblockchain */
void PruneBlockFilesManual(int nManualPruneHeight)
{
    CValidationState state;
    FlushStateToDisk(state, FLUSH_STATE_NONE, nManualPruneHeight);
}

/* Calculate the block/rev files that should be deleted to remain under target*/
void FindFilesToPrune(std::set<int>& setFilesToPrune, uint64_t nPruneAfterHeight)
{
    LOCK2(cs_main, cs_LastBlockFile);
    if (chainActive.Tip() == NULL || nPruneTarget == 0) {
        return;
    }
    if ((uint64_t)chainActive.Height() <= nPruneAfterHeight) {
        return;
    }

    unsigned int nLastBlockWeCanPrune = chainActive.Height() - MIN_BLOCKS_TO_KEEP;
    uint64_t nCurrentUsage = CalculateCurrentUsage();
    // We don't check to prune until after we've allocated new space for files
    // So we should leave a buffer under our target to account for another allocation
    // before the next pruning.
    uint64_t nBuffer = BLOCKFILE_CHUNK_SIZE + UNDOFILE_CHUNK_SIZE;
    uint64_t nBytesToPrune;
    int count=0;

    if (nCurrentUsage + nBuffer >= nPruneTarget) {
        for (int fileNumber = 0; fileNumber < nLastBlockFile; fileNumber++) {
            nBytesToPrune = vinfoBlockFile[fileNumber].nSize + vinfoBlockFile[fileNumber].nUndoSize;

            if (vinfoBlockFile[fileNumber].nSize == 0)
                continue;

            if (nCurrentUsage + nBuffer < nPruneTarget)  // are we below our target?
                break;

            // don't prune files that could have a block within MIN_BLOCKS_TO_KEEP of the main chain's tip but keep scanning
            if (vinfoBlockFile[fileNumber].nHeightLast > nLastBlockWeCanPrune)
                continue;

            PruneOneBlockFile(fileNumber);
            // Queue up the files for removal
            setFilesToPrune.insert(fileNumber);
            nCurrentUsage -= nBytesToPrune;
            count++;
        }
    }

    LogPrint("prune", "Prune: target=%dMiB actual=%dMiB diff=%dMiB max_prune_height=%d removed %d blk/rev pairs\n",
           nPruneTarget/1024/1024, nCurrentUsage/1024/1024,
           ((int64_t)nPruneTarget - (int64_t)nCurrentUsage)/1024/1024,
           nLastBlockWeCanPrune, count);
}

bool CheckDiskSpace(uint64_t nAdditionalBytes)
{
    uint64_t nFreeBytesAvailable = boost::filesystem::space(GetDataDir()).available;

    // Check for nMinDiskSpace bytes (currently 50MB)
    if (nFreeBytesAvailable < nMinDiskSpace + nAdditionalBytes)
        return AbortNode("Disk space is low!", _("Error: Disk space is low!"));

    return true;
}

FILE* OpenDiskFile(const CDiskBlockPos &pos, const char *prefix, bool fReadOnly)
{
    if (pos.IsNull())
        return NULL;
    boost::filesystem::path path = GetBlockPosFilename(pos, prefix);
    boost::filesystem::create_directories(path.parent_path());
    FILE* file = fopen(path.string().c_str(), "rb+");
    if (!file && !fReadOnly)
        file = fopen(path.string().c_str(), "wb+");
    if (!file) {
        LogPrintf("Unable to open file %s\n", path.string());
        return NULL;
    }
    if (pos.nPos) {
        if (fseek(file, pos.nPos, SEEK_SET)) {
            LogPrintf("Unable to seek to position %u of %s\n", pos.nPos, path.string());
            fclose(file);
            return NULL;
        }
    }
    return file;
}

FILE* OpenBlockFile(const CDiskBlockPos &pos, bool fReadOnly) {
    return OpenDiskFile(pos, "blk", fReadOnly);
}

FILE* OpenUndoFile(const CDiskBlockPos &pos, bool fReadOnly) {
    return OpenDiskFile(pos, "rev", fReadOnly);
}

boost::filesystem::path GetBlockPosFilename(const CDiskBlockPos &pos, const char *prefix)
{
    return GetDataDir() / "blocks" / strprintf("%s%05u.dat", prefix, pos.nFile);
}

CBlockIndex * InsertBlockIndex(uint256 hash)
{
    if (hash.IsNull())
        return NULL;

    // Return existing
    BlockMap::iterator mi = mapBlockIndex.find(hash);
    if (mi != mapBlockIndex.end())
        return (*mi).second;

    // Create new
    CBlockIndex* pindexNew = new CBlockIndex();
    if (!pindexNew)
        throw std::runtime_error(std::string(__func__) + ": new CBlockIndex failed");
    mi = mapBlockIndex.insert(std::make_pair(hash, pindexNew)).first;
    pindexNew->phashBlock = &((*mi).first);

    return pindexNew;
}

bool static LoadBlockIndexDB(const CChainParams& chainparams)
{
    if (!pblocktree->LoadBlockIndexGuts(InsertBlockIndex))
        return false;

    boost::this_thread::interruption_point();

    // Calculate nChainWork
    std::vector<std::pair<int, CBlockIndex*> > vSortedByHeight;
    vSortedByHeight.reserve(mapBlockIndex.size());
    BOOST_FOREACH(const PAIRTYPE(uint256, CBlockIndex*)& item, mapBlockIndex)
    {
        CBlockIndex* pindex = item.second;
        vSortedByHeight.push_back(std::make_pair(pindex->nHeight, pindex));
    }
    sort(vSortedByHeight.begin(), vSortedByHeight.end());
    BOOST_FOREACH(const PAIRTYPE(int, CBlockIndex*)& item, vSortedByHeight)
    {
        CBlockIndex* pindex = item.second;
        pindex->nChainWork = (pindex->pprev ? pindex->pprev->nChainWork : 0) + GetBlockProof(*pindex);
        pindex->nTimeMax = (pindex->pprev ? std::max(pindex->pprev->nTimeMax, pindex->nTime) : pindex->nTime);
        // We can link the chain of blocks for which we've received transactions at some point.
        // Pruned nodes may have deleted the block.
        if (pindex->nTx > 0) {
            if (pindex->pprev) {
                if (pindex->pprev->nChainTx) {
                    pindex->nChainTx = pindex->pprev->nChainTx + pindex->nTx;
                } else {
                    pindex->nChainTx = 0;
                    mapBlocksUnlinked.insert(std::make_pair(pindex->pprev, pindex));
                }
            } else {
                pindex->nChainTx = pindex->nTx;
            }
            if (!(pindex->nStatus & BLOCK_FAILED_MASK) && pindex->pprev && (pindex->pprev->nStatus & BLOCK_FAILED_MASK)) {
                LogPrintf("Invalid Block %s.", pindex->GetBlockHash().ToString() );
                pindex->nStatus |= BLOCK_FAILED_CHILD;
                setDirtyBlockIndex.insert(pindex);
            }
        }
        if (pindex->IsValid(BLOCK_VALID_TRANSACTIONS) && (pindex->nChainTx || pindex->pprev == NULL))
            setBlockIndexCandidates.insert(pindex);
        if (pindex->nStatus & BLOCK_FAILED_MASK && (!pindexBestInvalid || pindex->nChainWork > pindexBestInvalid->nChainWork))
            pindexBestInvalid = pindex;
        if (pindex->pprev)
            pindex->BuildSkip();
        if (pindex->IsValid(BLOCK_VALID_TREE) && (pindexBestHeader == NULL || CBlockIndexWorkComparator()(pindexBestHeader, pindex)))
            pindexBestHeader = pindex;
    }

    // Load block file info
    pblocktree->ReadLastBlockFile(nLastBlockFile);
    vinfoBlockFile.resize(nLastBlockFile + 1);
    LogPrintf("%s: last block file = %i\n", __func__, nLastBlockFile);
    for (int nFile = 0; nFile <= nLastBlockFile; nFile++) {
        pblocktree->ReadBlockFileInfo(nFile, vinfoBlockFile[nFile]);
    }
    LogPrintf("%s: last block file info: %s\n", __func__, vinfoBlockFile[nLastBlockFile].ToString());
    for (int nFile = nLastBlockFile + 1; true; nFile++) {
        CBlockFileInfo info;
        if (pblocktree->ReadBlockFileInfo(nFile, info)) {
            vinfoBlockFile.push_back(info);
        } else {
            break;
        }
    }

    // Check presence of blk files
    LogPrintf("Checking all blk files are present...\n");
    std::set<int> setBlkDataFiles;
    BOOST_FOREACH(const PAIRTYPE(uint256, CBlockIndex*)& item, mapBlockIndex)
    {
        CBlockIndex* pindex = item.second;
        if (pindex->nStatus & BLOCK_HAVE_DATA) {
            setBlkDataFiles.insert(pindex->nFile);
        }
    }
    for (std::set<int>::iterator it = setBlkDataFiles.begin(); it != setBlkDataFiles.end(); it++)
    {
        CDiskBlockPos pos(*it, 0);
        if (CAutoFile(OpenBlockFile(pos, true), SER_DISK, CLIENT_VERSION).IsNull()) {
            return false;
        }
    }

    // Check whether we have ever pruned block & undo files
    pblocktree->ReadFlag("prunedblockfiles", fHavePruned);
    if (fHavePruned)
        LogPrintf("LoadBlockIndexDB(): Block files have previously been pruned\n");

    // Check whether we need to continue reindexing
    bool fReindexing = false;
    pblocktree->ReadReindexing(fReindexing);
    fReindex |= fReindexing;

    // Check whether we have a transaction index
    pblocktree->ReadFlag("txindex", fTxIndex);
    LogPrintf("%s: transaction index %s\n", __func__, fTxIndex ? "enabled" : "disabled");

    // Load pointer to end of best chain
    BlockMap::iterator it = mapBlockIndex.find(pcoinsTip->GetBestBlock());
    if (it == mapBlockIndex.end())
        return true;
    chainActive.SetTip(it->second);

    PruneBlockIndexCandidates();

    LogPrintf("%s: hashBestChain=%s height=%d date=%s progress=%f\n", __func__,
        chainActive.Tip()->GetBlockHash().ToString(), chainActive.Height(),
        DateTimeStrFormat("%Y-%m-%d %H:%M:%S", chainActive.Tip()->GetBlockTime()),
        GuessVerificationProgress(chainparams.TxData(), chainActive.Tip()));

    return true;
}

CVerifyDB::CVerifyDB()
{
    uiInterface.ShowProgress(_("Verifying blocks..."), 0);
}

CVerifyDB::~CVerifyDB()
{
    uiInterface.ShowProgress("", 100);
}

bool CVerifyDB::VerifyDB(const CChainParams& chainparams, CCoinsView *coinsview, int nCheckLevel, int nCheckDepth)
{
    LOCK(cs_main);
    if (chainActive.Tip() == NULL || chainActive.Tip()->pprev == NULL)
        return true;

    // Verify blocks in the best chain
    if (nCheckDepth <= 0)
        nCheckDepth = 1000000000; // suffices until the year 19000
    if (nCheckDepth > chainActive.Height())
        nCheckDepth = chainActive.Height();
    nCheckLevel = std::max(0, std::min(4, nCheckLevel));
    LogPrintf("Verifying last %i blocks at level %i\n", nCheckDepth, nCheckLevel);
    CCoinsViewCache coins(coinsview);
    CBlockIndex* pindexState = chainActive.Tip();
    CBlockIndex* pindexFailure = NULL;
    int nGoodTransactions = 0;
    CValidationState state;
    int reportDone = 0;
    LogPrintf("[0%%]...");
    for (CBlockIndex* pindex = chainActive.Tip(); pindex && pindex->pprev; pindex = pindex->pprev)
    {
        boost::this_thread::interruption_point();
        int percentageDone = std::max(1, std::min(99, (int)(((double)(chainActive.Height() - pindex->nHeight)) / (double)nCheckDepth * (nCheckLevel >= 4 ? 50 : 100))));
        if (reportDone < percentageDone/10) {
            // report every 10% step
            LogPrintf("[%d%%]...", percentageDone);
            reportDone = percentageDone/10;
        }
        uiInterface.ShowProgress(_("Verifying blocks..."), percentageDone);
        if (pindex->nHeight < chainActive.Height()-nCheckDepth)
            break;
        if (fPruneMode && !(pindex->nStatus & BLOCK_HAVE_DATA)) {
            // If pruning, only go back as far as we have data.
            LogPrintf("VerifyDB(): block verification stopping at height %d (pruning, no data)\n", pindex->nHeight);
            break;
        }
        CBlock block;
        // check level 0: read from disk
        if (!ReadBlockFromDisk(block, pindex, chainparams.GetConsensus(pindex->nHeight)))
            return error("VerifyDB(): *** ReadBlockFromDisk failed at %d, hash=%s", pindex->nHeight, pindex->GetBlockHash().ToString());
        // check level 1: verify block validity
        if (nCheckLevel >= 1 && !CheckBlock(block, state))
            return error("%s: *** found bad block at %d, hash=%s (%s)\n", __func__,
                         pindex->nHeight, pindex->GetBlockHash().ToString(), FormatStateMessage(state));
        // check level 2: verify undo validity
        if (nCheckLevel >= 2 && pindex) {
            CBlockUndo undo;
            CDiskBlockPos pos = pindex->GetUndoPos();
            if (!pos.IsNull()) {
                if (!UndoReadFromDisk(undo, pos, pindex->pprev->GetBlockHash()))
                    return error("VerifyDB(): *** found bad undo data at %d, hash=%s\n", pindex->nHeight, pindex->GetBlockHash().ToString());
            }
        }
        // check level 3: check for inconsistencies during memory-only disconnect of tip blocks
        if (nCheckLevel >= 3 && pindex == pindexState && (coins.DynamicMemoryUsage() + pcoinsTip->DynamicMemoryUsage()) <= nCoinCacheUsage) {
            bool fClean = true;
            if (!DisconnectBlock(block, state, pindex, coins, &fClean))
                return error("VerifyDB(): *** irrecoverable inconsistency in block data at %d, hash=%s", pindex->nHeight, pindex->GetBlockHash().ToString());
            pindexState = pindex->pprev;
            if (!fClean) {
                nGoodTransactions = 0;
                pindexFailure = pindex;
            } else
                nGoodTransactions += block.vtx.size();
        }
        if (ShutdownRequested())
            return true;
    }
    if (pindexFailure)
        return error("VerifyDB(): *** coin database inconsistencies found (last %i blocks, %i good transactions before that)\n", chainActive.Height() - pindexFailure->nHeight + 1, nGoodTransactions);

    // check level 4: try reconnecting blocks
    if (nCheckLevel >= 4) {
        CBlockIndex *pindex = pindexState;
        while (pindex != chainActive.Tip()) {
            boost::this_thread::interruption_point();
            uiInterface.ShowProgress(_("Verifying blocks..."), std::max(1, std::min(99, 100 - (int)(((double)(chainActive.Height() - pindex->nHeight)) / (double)nCheckDepth * 50))));
            pindex = chainActive.Next(pindex);
            CBlock block;
            if (!ReadBlockFromDisk(block, pindex, chainparams.GetConsensus(pindex->nHeight)))
                return error("VerifyDB(): *** ReadBlockFromDisk failed at %d, hash=%s", pindex->nHeight, pindex->GetBlockHash().ToString());
            if (!ConnectBlock(block, state, pindex, coins, chainparams))
                return error("VerifyDB(): *** found unconnectable block at %d, hash=%s", pindex->nHeight, pindex->GetBlockHash().ToString());
        }
    }

    LogPrintf("[DONE].\n");
    LogPrintf("No coin database inconsistencies in last %i blocks (%i transactions)\n", chainActive.Height() - pindexState->nHeight, nGoodTransactions);

    return true;
}

bool RewindBlockIndex(const CChainParams& params)
{
    LOCK(cs_main);

    int nHeight = 1;
    while (nHeight <= chainActive.Height()) {
        if (IsWitnessEnabled(chainActive[nHeight - 1], params.GetConsensus(nHeight - 1)) && !(chainActive[nHeight]->nStatus & BLOCK_OPT_WITNESS)) {
            break;
        }
        nHeight++;
    }

    // nHeight is now the height of the first insufficiently-validated block, or tipheight + 1
    CValidationState state;
    CBlockIndex* pindex = chainActive.Tip();
    while (chainActive.Height() >= nHeight) {
        if (fPruneMode && !(chainActive.Tip()->nStatus & BLOCK_HAVE_DATA)) {
            // If pruning, don't try rewinding past the HAVE_DATA point;
            // since older blocks can't be served anyway, there's
            // no need to walk further, and trying to DisconnectTip()
            // will fail (and require a needless reindex/redownload
            // of the blockchain).
            break;
        }
        if (!DisconnectTip(state, params, true)) {
            return error("RewindBlockIndex: unable to disconnect block at height %i", pindex->nHeight);
        }
        // Occasionally flush state to disk.
        if (!FlushStateToDisk(state, FLUSH_STATE_PERIODIC))
            return false;
    }

    // Reduce validity flag and have-data flags.
    // We do this after actual disconnecting, otherwise we'll end up writing the lack of data
    // to disk before writing the chainstate, resulting in a failure to continue if interrupted.
    for (BlockMap::iterator it = mapBlockIndex.begin(); it != mapBlockIndex.end(); it++) {
        CBlockIndex* pindexIter = it->second;

        // Note: If we encounter an insufficiently validated block that
        // is on chainActive, it must be because we are a pruning node, and
        // this block or some successor doesn't HAVE_DATA, so we were unable to
        // rewind all the way.  Blocks remaining on chainActive at this point
        // must not have their validity reduced.
        if (IsWitnessEnabled(pindexIter->pprev, params.GetConsensus(pindexIter->nHeight)) && !(pindexIter->nStatus & BLOCK_OPT_WITNESS) && !chainActive.Contains(pindexIter)) {
            // Reduce validity
            pindexIter->nStatus = std::min<unsigned int>(pindexIter->nStatus & BLOCK_VALID_MASK, BLOCK_VALID_TREE) | (pindexIter->nStatus & ~BLOCK_VALID_MASK);
            // Remove have-data flags.
            pindexIter->nStatus &= ~(BLOCK_HAVE_DATA | BLOCK_HAVE_UNDO);
            // Remove storage location.
            pindexIter->nFile = 0;
            pindexIter->nDataPos = 0;
            pindexIter->nUndoPos = 0;
            // Remove various other things
            pindexIter->nTx = 0;
            pindexIter->nChainTx = 0;
            pindexIter->nSequenceId = 0;
            // Make sure it gets written.
            setDirtyBlockIndex.insert(pindexIter);
            // Update indexes
            setBlockIndexCandidates.erase(pindexIter);
            std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> ret = mapBlocksUnlinked.equal_range(pindexIter->pprev);
            while (ret.first != ret.second) {
                if (ret.first->second == pindexIter) {
                    mapBlocksUnlinked.erase(ret.first++);
                } else {
                    ++ret.first;
                }
            }
        } else if (pindexIter->IsValid(BLOCK_VALID_TRANSACTIONS) && pindexIter->nChainTx) {
            setBlockIndexCandidates.insert(pindexIter);
        }
    }

    PruneBlockIndexCandidates();

    CheckBlockIndex(params.GetConsensus(chainActive.Height()));

    if (!FlushStateToDisk(state, FLUSH_STATE_ALWAYS)) {
        return false;
    }

    return true;
}

// May NOT be used after any connections are up as much
// of the peer-processing logic assumes a consistent
// block index state
void UnloadBlockIndex()
{
    LOCK(cs_main);
    setBlockIndexCandidates.clear();
    chainActive.SetTip(NULL);
    pindexBestInvalid = NULL;
    pindexBestHeader = NULL;
    mempool.clear();
    mapBlocksUnlinked.clear();
    vinfoBlockFile.clear();
    nLastBlockFile = 0;
    nBlockSequenceId = 1;
    setDirtyBlockIndex.clear();
    gFailedBlocks.clear();
    setDirtyFileInfo.clear();
    versionbitscache.Clear();
    for (int b = 0; b < VERSIONBITS_NUM_BITS; b++) {
        warningcache[b].clear();
    }

    BOOST_FOREACH(BlockMap::value_type& entry, mapBlockIndex) {
        delete entry.second;
    }
    mapBlockIndex.clear();
    fHavePruned = false;
}

bool LoadBlockIndex(const CChainParams& chainparams)
{
    // Load block index from databases
    if (!fReindex && !LoadBlockIndexDB(chainparams))
        return false;
    return true;
}

bool InitBlockIndex(const CChainParams& chainparams)
{
    LOCK(cs_main);

    // Check whether we're already initialized
    if (chainActive.Genesis() != NULL)
        return true;

    // Use the provided setting for -txindex in the new database
    fTxIndex = GetBoolArg("-txindex", DEFAULT_TXINDEX);
    pblocktree->WriteFlag("txindex", fTxIndex);
    LogPrintf("Initializing databases...\n");

    // Only add the genesis block if not reindexing (in which case we reuse the one already on disk)
    if (!fReindex) {
        try {
            CBlock &block = const_cast<CBlock&>(chainparams.GenesisBlock());
            // Start new block file
            unsigned int nBlockSize = ::GetSerializeSize(block, SER_DISK, CLIENT_VERSION);
            CDiskBlockPos blockPos;
            CValidationState state;
            if (!FindBlockPos(state, blockPos, nBlockSize+8, 0, block.GetBlockTime()))
                return error("LoadBlockIndex(): FindBlockPos failed");
            if (!WriteBlockToDisk(block, blockPos, chainparams.MessageStart()))
                return error("LoadBlockIndex(): writing genesis block to disk failed");
            CBlockIndex *pindex = AddToBlockIndex(block);
            if (!ReceivedBlockTransactions(block, state, pindex, blockPos))
                return error("LoadBlockIndex(): genesis block not accepted");
            // Force a chainstate write so that when we VerifyDB in a moment, it doesn't check stale data
            return FlushStateToDisk(state, FLUSH_STATE_ALWAYS);
        } catch (const std::runtime_error& e) {
            return error("LoadBlockIndex(): failed to initialize block database: %s", e.what());
        }
    }

    return true;
}

bool LoadExternalBlockFile(const CChainParams& chainparams, FILE* fileIn, CDiskBlockPos *dbp)
{
    // Map of disk positions for blocks with unknown parent (only used for reindex)
    static std::multimap<uint256, CDiskBlockPos> mapBlocksUnknownParent;
    int64_t nStart = GetTimeMillis();

    int nLoaded = 0;
    try {
        // This takes over fileIn and calls fclose() on it in the CBufferedFile destructor
        CBufferedFile blkdat(fileIn, 2*MAX_BLOCK_SERIALIZED_SIZE, MAX_BLOCK_SERIALIZED_SIZE+8, SER_DISK, CLIENT_VERSION);
        uint64_t nRewind = blkdat.GetPos();
        while (!blkdat.eof()) {
            boost::this_thread::interruption_point();

            blkdat.SetPos(nRewind);
            nRewind++; // start one byte further next time, in case of failure
            blkdat.SetLimit(); // remove former limit
            unsigned int nSize = 0;
            try {
                // locate a header
                unsigned char buf[CMessageHeader::MESSAGE_START_SIZE];
                blkdat.FindByte(chainparams.MessageStart()[0]);
                nRewind = blkdat.GetPos()+1;
                blkdat >> FLATDATA(buf);
                if (memcmp(buf, chainparams.MessageStart(), CMessageHeader::MESSAGE_START_SIZE))
                    continue;
                // read size
                blkdat >> nSize;
                if (nSize < 80 || nSize > MAX_BLOCK_SERIALIZED_SIZE)
                    continue;
            } catch (const std::exception&) {
                // no valid block header found; don't complain
                break;
            }
            try {
                // read block
                uint64_t nBlockPos = blkdat.GetPos();
                if (dbp)
                    dbp->nPos = nBlockPos;
                blkdat.SetLimit(nBlockPos + nSize);
                blkdat.SetPos(nBlockPos);
                std::shared_ptr<CBlock> pblock = std::make_shared<CBlock>();
                CBlock& block = *pblock;
                blkdat >> block;
                nRewind = blkdat.GetPos();

                // detect out of order blocks, and store them for later
                uint256 hash = block.GetHash();
                if (hash != chainparams.GetConsensus(0).hashGenesisBlock && mapBlockIndex.find(block.hashPrevBlock) == mapBlockIndex.end()) {
                    LogPrint("reindex", "%s: Out of order block %s, parent %s not known\n", __func__, hash.ToString(),
                            block.hashPrevBlock.ToString());
                    if (dbp)
                        mapBlocksUnknownParent.insert(std::make_pair(block.hashPrevBlock, *dbp));
                    continue;
                }

                // process in case the block isn't known yet
                if (mapBlockIndex.count(hash) == 0 || (mapBlockIndex[hash]->nStatus & BLOCK_HAVE_DATA) == 0) {
                    LOCK(cs_main);
                    CValidationState state;
                    if (AcceptBlock(pblock, state, chainparams, NULL, true, dbp, NULL))
                        nLoaded++;
                    if (state.IsError())
                        break;
                } else if (hash != chainparams.GetConsensus(0).hashGenesisBlock && mapBlockIndex[hash]->nHeight % 1000 == 0) {
                    LogPrint("reindex", "Block Import: already had block %s at height %d\n", hash.ToString(), mapBlockIndex[hash]->nHeight);
                }

                // Activate the genesis block so normal node progress can continue
                if (hash == chainparams.GetConsensus(0).hashGenesisBlock) {
                    CValidationState state;
                    if (!ActivateBestChain(state, chainparams)) {
                        break;
                    }
                }

                NotifyHeaderTip();

                // Recursively process earlier encountered successors of this block
                std::deque<uint256> queue;
                queue.push_back(hash);
                while (!queue.empty()) {
                    uint256 head = queue.front();
                    queue.pop_front();
                    std::pair<std::multimap<uint256, CDiskBlockPos>::iterator, std::multimap<uint256, CDiskBlockPos>::iterator> range = mapBlocksUnknownParent.equal_range(head);
                    while (range.first != range.second) {
                        std::multimap<uint256, CDiskBlockPos>::iterator it = range.first;
                        std::shared_ptr<CBlock> pblockrecursive = std::make_shared<CBlock>();
                        // TODO: Need a valid consensus height
                        if (ReadBlockFromDisk(*pblockrecursive, it->second, chainparams.GetConsensus(0)))
                        {
                            LogPrint("reindex", "%s: Processing out of order child %s of %s\n", __func__, pblockrecursive->GetHash().ToString(),
                                    head.ToString());
                            LOCK(cs_main);
                            CValidationState dummy;
                            if (AcceptBlock(pblockrecursive, dummy, chainparams, NULL, true, &it->second, NULL))
                            {
                                nLoaded++;
                                queue.push_back(pblockrecursive->GetHash());
                            }
                        }
                        range.first++;
                        mapBlocksUnknownParent.erase(it);
                        NotifyHeaderTip();
                    }
                }
            } catch (const std::exception& e) {
                LogPrintf("%s: Deserialize or I/O error - %s\n", __func__, e.what());
            }
        }
    } catch (const std::runtime_error& e) {
        AbortNode(std::string("System error: ") + e.what());
    }
    if (nLoaded > 0)
        LogPrintf("Loaded %i blocks from external file in %dms\n", nLoaded, GetTimeMillis() - nStart);
    return nLoaded > 0;
}

void static CheckBlockIndex(const Consensus::Params& consensusParams)
{
    if (!fCheckBlockIndex) {
        return;
    }

    LOCK(cs_main);

    // During a reindex, we read the genesis block and call CheckBlockIndex before ActivateBestChain,
    // so we have the genesis block in mapBlockIndex but no active chain.  (A few of the tests when
    // iterating the block tree require that chainActive has been initialized.)
    if (chainActive.Height() < 0) {
        assert(mapBlockIndex.size() <= 1);
        return;
    }

    // Build forward-pointing map of the entire block tree.
    std::multimap<CBlockIndex*,CBlockIndex*> forward;
    for (BlockMap::iterator it = mapBlockIndex.begin(); it != mapBlockIndex.end(); it++) {
        forward.insert(std::make_pair(it->second->pprev, it->second));
    }

    assert(forward.size() == mapBlockIndex.size());

    std::pair<std::multimap<CBlockIndex*,CBlockIndex*>::iterator,std::multimap<CBlockIndex*,CBlockIndex*>::iterator> rangeGenesis = forward.equal_range(NULL);
    CBlockIndex *pindex = rangeGenesis.first->second;
    rangeGenesis.first++;
    assert(rangeGenesis.first == rangeGenesis.second); // There is only one index entry with parent NULL.

    // Iterate over the entire block tree, using depth-first search.
    // Along the way, remember whether there are blocks on the path from genesis
    // block being explored which are the first to have certain properties.
    size_t nNodes = 0;
    int nHeight = 0;
    CBlockIndex* pindexFirstInvalid = NULL; // Oldest ancestor of pindex which is invalid.
    CBlockIndex* pindexFirstMissing = NULL; // Oldest ancestor of pindex which does not have BLOCK_HAVE_DATA.
    CBlockIndex* pindexFirstNeverProcessed = NULL; // Oldest ancestor of pindex for which nTx == 0.
    CBlockIndex* pindexFirstNotTreeValid = NULL; // Oldest ancestor of pindex which does not have BLOCK_VALID_TREE (regardless of being valid or not).
    CBlockIndex* pindexFirstNotTransactionsValid = NULL; // Oldest ancestor of pindex which does not have BLOCK_VALID_TRANSACTIONS (regardless of being valid or not).
    CBlockIndex* pindexFirstNotChainValid = NULL; // Oldest ancestor of pindex which does not have BLOCK_VALID_CHAIN (regardless of being valid or not).
    CBlockIndex* pindexFirstNotScriptsValid = NULL; // Oldest ancestor of pindex which does not have BLOCK_VALID_SCRIPTS (regardless of being valid or not).
    while (pindex != NULL) {
        nNodes++;
        if (pindexFirstInvalid == NULL && pindex->nStatus & BLOCK_FAILED_VALID) pindexFirstInvalid = pindex;
        if (pindexFirstMissing == NULL && !(pindex->nStatus & BLOCK_HAVE_DATA)) pindexFirstMissing = pindex;
        if (pindexFirstNeverProcessed == NULL && pindex->nTx == 0) pindexFirstNeverProcessed = pindex;
        if (pindex->pprev != NULL && pindexFirstNotTreeValid == NULL && (pindex->nStatus & BLOCK_VALID_MASK) < BLOCK_VALID_TREE) pindexFirstNotTreeValid = pindex;
        if (pindex->pprev != NULL && pindexFirstNotTransactionsValid == NULL && (pindex->nStatus & BLOCK_VALID_MASK) < BLOCK_VALID_TRANSACTIONS) pindexFirstNotTransactionsValid = pindex;
        if (pindex->pprev != NULL && pindexFirstNotChainValid == NULL && (pindex->nStatus & BLOCK_VALID_MASK) < BLOCK_VALID_CHAIN) pindexFirstNotChainValid = pindex;
        if (pindex->pprev != NULL && pindexFirstNotScriptsValid == NULL && (pindex->nStatus & BLOCK_VALID_MASK) < BLOCK_VALID_SCRIPTS) pindexFirstNotScriptsValid = pindex;

        // Begin: actual consistency checks.
        if (pindex->pprev == NULL) {
            // Genesis block checks.
            assert(pindex->GetBlockHash() == consensusParams.hashGenesisBlock); // Genesis block's hash must match.
            assert(pindex == chainActive.Genesis()); // The current active chain's genesis block must be this block.
        }
        if (pindex->nChainTx == 0) assert(pindex->nSequenceId <= 0);  // nSequenceId can't be set positive for blocks that aren't linked (negative is used for preciousblock)
        // VALID_TRANSACTIONS is equivalent to nTx > 0 for all nodes (whether or not pruning has occurred).
        // HAVE_DATA is only equivalent to nTx > 0 (or VALID_TRANSACTIONS) if no pruning has occurred.
        if (!fHavePruned) {
            // If we've never pruned, then HAVE_DATA should be equivalent to nTx > 0
            assert(!(pindex->nStatus & BLOCK_HAVE_DATA) == (pindex->nTx == 0));
            assert(pindexFirstMissing == pindexFirstNeverProcessed);
        } else {
            // If we have pruned, then we can only say that HAVE_DATA implies nTx > 0
            if (pindex->nStatus & BLOCK_HAVE_DATA) assert(pindex->nTx > 0);
        }
        if (pindex->nStatus & BLOCK_HAVE_UNDO) assert(pindex->nStatus & BLOCK_HAVE_DATA);
        assert(((pindex->nStatus & BLOCK_VALID_MASK) >= BLOCK_VALID_TRANSACTIONS) == (pindex->nTx > 0)); // This is pruning-independent.
        // All parents having had data (at some point) is equivalent to all parents being VALID_TRANSACTIONS, which is equivalent to nChainTx being set.
        assert((pindexFirstNeverProcessed != NULL) == (pindex->nChainTx == 0)); // nChainTx != 0 is used to signal that all parent blocks have been processed (but may have been pruned).
        assert((pindexFirstNotTransactionsValid != NULL) == (pindex->nChainTx == 0));
        assert(pindex->nHeight == nHeight); // nHeight must be consistent.
        assert(pindex->pprev == NULL || pindex->nChainWork >= pindex->pprev->nChainWork); // For every block except the genesis block, the chainwork must be larger than the parent's.
        assert(nHeight < 2 || (pindex->pskip && (pindex->pskip->nHeight < nHeight))); // The pskip pointer must point back for all but the first 2 blocks.
        assert(pindexFirstNotTreeValid == NULL); // All mapBlockIndex entries must at least be TREE valid
        if ((pindex->nStatus & BLOCK_VALID_MASK) >= BLOCK_VALID_TREE) assert(pindexFirstNotTreeValid == NULL); // TREE valid implies all parents are TREE valid
        if ((pindex->nStatus & BLOCK_VALID_MASK) >= BLOCK_VALID_CHAIN) assert(pindexFirstNotChainValid == NULL); // CHAIN valid implies all parents are CHAIN valid
        if ((pindex->nStatus & BLOCK_VALID_MASK) >= BLOCK_VALID_SCRIPTS) assert(pindexFirstNotScriptsValid == NULL); // SCRIPTS valid implies all parents are SCRIPTS valid
        if (pindexFirstInvalid == NULL) {
            // Checks for not-invalid blocks.
            assert((pindex->nStatus & BLOCK_FAILED_MASK) == 0); // The failed mask cannot be set for blocks without invalid parents.
        }
        if (!CBlockIndexWorkComparator()(pindex, chainActive.Tip()) && pindexFirstNeverProcessed == NULL) {
            if (pindexFirstInvalid == NULL) {
                // If this block sorts at least as good as the current tip and
                // is valid and we have all data for its parents, it must be in
                // setBlockIndexCandidates.  chainActive.Tip() must also be there
                // even if some data has been pruned.
                if (pindexFirstMissing == NULL || pindex == chainActive.Tip()) {
                    assert(setBlockIndexCandidates.count(pindex));
                }
                // If some parent is missing, then it could be that this block was in
                // setBlockIndexCandidates but had to be removed because of the missing data.
                // In this case it must be in mapBlocksUnlinked -- see test below.
            }
        } else { // If this block sorts worse than the current tip or some ancestor's block has never been seen, it cannot be in setBlockIndexCandidates.
            assert(setBlockIndexCandidates.count(pindex) == 0);
        }
        // Check whether this block is in mapBlocksUnlinked.
        std::pair<std::multimap<CBlockIndex*,CBlockIndex*>::iterator,std::multimap<CBlockIndex*,CBlockIndex*>::iterator> rangeUnlinked = mapBlocksUnlinked.equal_range(pindex->pprev);
        bool foundInUnlinked = false;
        while (rangeUnlinked.first != rangeUnlinked.second) {
            assert(rangeUnlinked.first->first == pindex->pprev);
            if (rangeUnlinked.first->second == pindex) {
                foundInUnlinked = true;
                break;
            }
            rangeUnlinked.first++;
        }
        if (pindex->pprev && (pindex->nStatus & BLOCK_HAVE_DATA) && pindexFirstNeverProcessed != NULL && pindexFirstInvalid == NULL) {
            // If this block has block data available, some parent was never received, and has no invalid parents, it must be in mapBlocksUnlinked.
            assert(foundInUnlinked);
        }
        if (!(pindex->nStatus & BLOCK_HAVE_DATA)) assert(!foundInUnlinked); // Can't be in mapBlocksUnlinked if we don't HAVE_DATA
        if (pindexFirstMissing == NULL) assert(!foundInUnlinked); // We aren't missing data for any parent -- cannot be in mapBlocksUnlinked.
        if (pindex->pprev && (pindex->nStatus & BLOCK_HAVE_DATA) && pindexFirstNeverProcessed == NULL && pindexFirstMissing != NULL) {
            // We HAVE_DATA for this block, have received data for all parents at some point, but we're currently missing data for some parent.
            assert(fHavePruned); // We must have pruned.
            // This block may have entered mapBlocksUnlinked if:
            //  - it has a descendant that at some point had more work than the
            //    tip, and
            //  - we tried switching to that descendant but were missing
            //    data for some intermediate block between chainActive and the
            //    tip.
            // So if this block is itself better than chainActive.Tip() and it wasn't in
            // setBlockIndexCandidates, then it must be in mapBlocksUnlinked.
            if (!CBlockIndexWorkComparator()(pindex, chainActive.Tip()) && setBlockIndexCandidates.count(pindex) == 0) {
                if (pindexFirstInvalid == NULL) {
                    assert(foundInUnlinked);
                }
            }
        }
        // assert(pindex->GetBlockHash() == pindex->GetBlockHeader().GetHash()); // Perhaps too slow
        // End: actual consistency checks.

        // Try descending into the first subnode.
        std::pair<std::multimap<CBlockIndex*,CBlockIndex*>::iterator,std::multimap<CBlockIndex*,CBlockIndex*>::iterator> range = forward.equal_range(pindex);
        if (range.first != range.second) {
            // A subnode was found.
            pindex = range.first->second;
            nHeight++;
            continue;
        }
        // This is a leaf node.
        // Move upwards until we reach a node of which we have not yet visited the last child.
        while (pindex) {
            // We are going to either move to a parent or a sibling of pindex.
            // If pindex was the first with a certain property, unset the corresponding variable.
            if (pindex == pindexFirstInvalid) pindexFirstInvalid = NULL;
            if (pindex == pindexFirstMissing) pindexFirstMissing = NULL;
            if (pindex == pindexFirstNeverProcessed) pindexFirstNeverProcessed = NULL;
            if (pindex == pindexFirstNotTreeValid) pindexFirstNotTreeValid = NULL;
            if (pindex == pindexFirstNotTransactionsValid) pindexFirstNotTransactionsValid = NULL;
            if (pindex == pindexFirstNotChainValid) pindexFirstNotChainValid = NULL;
            if (pindex == pindexFirstNotScriptsValid) pindexFirstNotScriptsValid = NULL;
            // Find our parent.
            CBlockIndex* pindexPar = pindex->pprev;
            // Find which child we just visited.
            std::pair<std::multimap<CBlockIndex*,CBlockIndex*>::iterator,std::multimap<CBlockIndex*,CBlockIndex*>::iterator> rangePar = forward.equal_range(pindexPar);
            while (rangePar.first->second != pindex) {
                assert(rangePar.first != rangePar.second); // Our parent must have at least the node we're coming from as child.
                rangePar.first++;
            }
            // Proceed to the next one.
            rangePar.first++;
            if (rangePar.first != rangePar.second) {
                // Move to the sibling.
                pindex = rangePar.first->second;
                break;
            } else {
                // Move up further.
                pindex = pindexPar;
                nHeight--;
                continue;
            }
        }
    }

    // Check that we actually traversed the entire map.
    assert(nNodes == forward.size());
}

std::string CBlockFileInfo::ToString() const
{
    return strprintf("CBlockFileInfo(blocks=%u, size=%u, heights=%u...%u, time=%s...%s)", nBlocks, nSize, nHeightFirst, nHeightLast, DateTimeStrFormat("%Y-%m-%d", nTimeFirst), DateTimeStrFormat("%Y-%m-%d", nTimeLast));
}

CBlockFileInfo* GetBlockFileInfo(size_t n)
{
    LOCK(cs_LastBlockFile);

    return &vinfoBlockFile.at(n);
}

ThresholdState VersionBitsTipState(const Consensus::Params& params, Consensus::DeploymentPos pos)
{
    LOCK(cs_main);
    return VersionBitsState(chainActive.Tip(), params, pos, versionbitscache);
}

int VersionBitsTipStateSinceHeight(const Consensus::Params& params, Consensus::DeploymentPos pos)
{
    LOCK(cs_main);
    return VersionBitsStateSinceHeight(chainActive.Tip(), params, pos, versionbitscache);
}

static const uint64_t MEMPOOL_DUMP_VERSION = 1;

bool LoadMempool(void)
{
    int64_t nExpiryTimeout = GetArg("-mempoolexpiry", DEFAULT_MEMPOOL_EXPIRY) * 60 * 60;
    FILE* filestr = fopen((GetDataDir() / "mempool.dat").string().c_str(), "rb");
    CAutoFile file(filestr, SER_DISK, CLIENT_VERSION);
    if (file.IsNull()) {
        LogPrintf("Failed to open mempool file from disk. Continuing anyway.\n");
        return false;
    }

    int64_t count = 0;
    int64_t skipped = 0;
    int64_t failed = 0;
    int64_t nNow = GetTime();

    try {
        uint64_t version;
        file >> version;
        if (version != MEMPOOL_DUMP_VERSION) {
            return false;
        }
        uint64_t num;
        file >> num;
        double prioritydummy = 0;
        while (num--) {
            CTransactionRef tx;
            int64_t nTime;
            int64_t nFeeDelta;
            file >> tx;
            file >> nTime;
            file >> nFeeDelta;

            CAmount amountdelta = nFeeDelta;
            if (amountdelta) {
                mempool.PrioritiseTransaction(tx->GetHash(), tx->GetHash().ToString(), prioritydummy, amountdelta);
            }
            CValidationState state;
            if (nTime + nExpiryTimeout > nNow) {
                LOCK(cs_main);
                AcceptToMemoryPoolWithTime(mempool, state, tx, true, NULL, nTime);
                if (state.IsValid()) {
                    ++count;
                } else {
                    ++failed;
                }
            } else {
                ++skipped;
            }
            if (ShutdownRequested())
                return false;
        }
        std::map<uint256, CAmount> mapDeltas;
        file >> mapDeltas;

        for (const auto& i : mapDeltas) {
            mempool.PrioritiseTransaction(i.first, i.first.ToString(), prioritydummy, i.second);
        }
    } catch (const std::exception& e) {
        LogPrintf("Failed to deserialize mempool data on disk: %s. Continuing anyway.\n", e.what());
        return false;
    }

    LogPrintf("Imported mempool transactions from disk: %i successes, %i failed, %i expired\n", count, failed, skipped);
    return true;
}

void DumpMempool(void)
{
    int64_t start = GetTimeMicros();

    std::map<uint256, CAmount> mapDeltas;
    std::vector<TxMempoolInfo> vinfo;

    {
        LOCK(mempool.cs);
        for (const auto &i : mempool.mapDeltas) {
            mapDeltas[i.first] = i.second.second;
        }
        vinfo = mempool.infoAll();
    }

    int64_t mid = GetTimeMicros();

    try {
        FILE* filestr = fopen((GetDataDir() / "mempool.dat.new").string().c_str(), "wb");
        if (!filestr) {
            return;
        }

        CAutoFile file(filestr, SER_DISK, CLIENT_VERSION);

        uint64_t version = MEMPOOL_DUMP_VERSION;
        file << version;

        file << (uint64_t)vinfo.size();
        for (const auto& i : vinfo) {
            file << *(i.tx);
            file << (int64_t)i.nTime;
            file << (int64_t)i.nFeeDelta;
            mapDeltas.erase(i.tx->GetHash());
        }

        file << mapDeltas;
        FileCommit(file.Get());
        file.fclose();
        RenameOver(GetDataDir() / "mempool.dat.new", GetDataDir() / "mempool.dat");
        int64_t last = GetTimeMicros();
        LogPrintf("Dumped mempool: %gs to copy, %gs to dump\n", (mid-start)*0.000001, (last-mid)*0.000001);
    } catch (const std::exception& e) {
        LogPrintf("Failed to dump mempool: %s. Continuing anyway.\n", e.what());
    }
}

//! Guess how far we are in the verification process at the given block index
double GuessVerificationProgress(const ChainTxData& data, CBlockIndex *pindex) {
    if (pindex == NULL)
        return 0.0;

    int64_t nNow = time(NULL);

    double fTxTotal;

    if (pindex->nChainTx <= data.nTxCount) {
        fTxTotal = data.nTxCount + (nNow - data.nTime) * data.dTxRate;
    } else {
        fTxTotal = pindex->nChainTx + (nNow - pindex->GetBlockTime()) * data.dTxRate;
    }

    return pindex->nChainTx / fTxTotal;
}

class CMainCleanup
{
public:
    CMainCleanup() {}
    ~CMainCleanup() {
        // block headers
        BlockMap::iterator it1 = mapBlockIndex.begin();
        for (; it1 != mapBlockIndex.end(); it1++)
            delete (*it1).second;
        mapBlockIndex.clear();
    }
} instance_of_cmaincleanup;
