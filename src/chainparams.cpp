// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Copyright (c) 2022 The Luckycoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "chainparams.h"
#include "consensus/merkle.h"

#include "tinyformat.h"
#include "util.h"
#include "utilstrencodings.h"

#include <assert.h>

#include <boost/assign/list_of.hpp>

#include "chainparamsseeds.h"

static CBlock CreateGenesisBlock(const char* pszTimestamp, const CScript& genesisOutputScript, uint32_t nTime, uint32_t nNonce, uint32_t nBits, int32_t nVersion, const CAmount& genesisReward)
{
    CMutableTransaction txNew;
    txNew.nVersion = 1;
    txNew.vin.resize(1);
    txNew.vout.resize(1);
    txNew.vin[0].scriptSig = CScript() << 486604799 << CScriptNum(4) << std::vector<unsigned char>((const unsigned char*)pszTimestamp, (const unsigned char*)pszTimestamp + strlen(pszTimestamp));
    txNew.vout[0].nValue = genesisReward;
    txNew.vout[0].scriptPubKey = genesisOutputScript;

    CBlock genesis;
    genesis.nTime    = nTime;
    genesis.nBits    = nBits;
    genesis.nNonce   = nNonce;
    genesis.nVersion = nVersion;
    genesis.vtx.push_back(MakeTransactionRef(std::move(txNew)));
    genesis.hashPrevBlock.SetNull();
    genesis.hashMerkleRoot = BlockMerkleRoot(genesis);
    return genesis;
}

/**
 * Build the genesis block. Note that the output of its generation
 * transaction cannot be spent since it did not originally exist in the
 * database.
 *
 * CBlock(hash=000000000019d6, ver=1, hashPrevBlock=00000000000000, hashMerkleRoot=4a5e1e, nTime=1386325540, nBits=0x1e0ffff0, nNonce=99943, vtx=1)
 *   CTransaction(hash=4a5e1e, ver=1, vin.size=1, vout.size=1, nLockTime=0)
 *     CTxIn(COutPoint(000000, -1), coinbase 04ffff001d0104455468652054696d65732030332f4a616e2f32303039204368616e63656c6c6f72206f6e206272696e6b206f66207365636f6e64206261696c6f757420666f722062616e6b73)
 *     CTxOut(nValue=50.00000000, scriptPubKey=0x5F1DF16B2B704C8A578D0B)
 *   vMerkleTree: 4a5e1e
 */
static CBlock CreateGenesisBlock(uint32_t nTime, uint32_t nNonce, uint32_t nBits, int32_t nVersion, const CAmount& genesisReward)
{
    const char* pszTimestamp = "May 22, 2013, 12:16 a.m. EDT: Japan\x92s Nikkei Stock Average JP:NIK +1.77%, which ended at their highest level in more than five years in each of the last three trading sessions, climbed a further 1.2% Wednesday";
    const CScript genesisOutputScript = CScript() << ParseHex("040184710fa689ad5023690c80f3a49c8f13f8d45b8c857fbcbc8bc4a8e4d3eb4b10f4d4604fa08dce601aaf0f470216fe1b51850b4acf21b179c45070ac7b03a9") << OP_CHECKSIG;
    return CreateGenesisBlock(pszTimestamp, genesisOutputScript, nTime, nNonce, nBits, nVersion, genesisReward);
}

/**
 * Main network
 */
/**
 * What makes a good checkpoint block?
 * + Is surrounded by blocks with reasonable timestamps
 *   (no blocks before with a timestamp after, none after with
 *    timestamp before)
 * + Contains no strange transactions
 */

class CMainParams : public CChainParams {
private:
    Consensus::Params digishieldConsensus;
    Consensus::Params auxpowConsensus;
public:
    CMainParams() {
        strNetworkID = "main";

        // Blocks 0 - 69359 are conventional difficulty calculation
        consensus.nSubsidyHalvingInterval = 100000;
        consensus.nMajorityEnforceBlockUpgrade = 1500;
        consensus.nMajorityRejectBlockOutdated = 1900;
        consensus.nMajorityWindow = 2000;
        // After deployments are activated we can change it
        consensus.BIP34Height = 95551;
        consensus.BIP34Hash = uint256S("0xd45224f678ed82cf7378e684fa6dc020ec35fd3360059f16d058200dbd0cc3d6"); // 95551
        consensus.BIP65Height = 95551;
        consensus.BIP66Height = 95551;
        consensus.powLimit = uint256S("0x00000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"); // ~uint256(0) >> 20;
        consensus.nPowTargetTimespan = 4 * 60 * 60; // pre-digishield: 4 hours
        consensus.nPowTargetSpacing = 60; // 1 minute
        consensus.fDigishieldDifficultyCalculation = false;
        consensus.nCoinbaseMaturity = 70;
        consensus.fPowAllowMinDifficultyBlocks = false;
        consensus.fPowAllowDigishieldMinDifficultyBlocks = false;
        consensus.fPowNoRetargeting = false;
        consensus.nRuleChangeActivationThreshold = 9576; // 95% of 10,080
        consensus.nMinerConfirmationWindow = 10080; // 60 * 24 * 7 = 10,080 blocks, or one week
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = 1199145601; // January 1, 2008
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = 1230767999; // December 31, 2008

        // Deployment of BIP68, BIP112, and BIP113.
        // XXX: BIP heights and hashes all need to be updated to Luckycoin values
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].bit = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nStartTime = 1725497122; // Sep 05 2024 00:45:22
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nTimeout = 1788569122; // Sep 05 2026 00:45:22

        // Deployment of SegWit (BIP141, BIP143, and BIP147)
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].bit = 1;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nStartTime = 1725497122; // Sep 05 2024 00:45:22
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nTimeout = 1788569122; // Sep 05 2026 00:45:22

        // The best chain should have at least this much work.
        consensus.nMinimumChainWork = uint256S("0x000000000000000000000000000000000000000000000c6764d4993a848f6f28"); // 620035

        // By default assume that the signatures in ancestors of this block are valid.
        consensus.defaultAssumeValid = uint256S("b0678b12f01fd01f4f6b93f2f6fe63435a50c06c302b8daff59ba8de77a646fd"); // 620035

        // AuxPoW parameters
        consensus.nAuxpowChainId = 0x2013;
        consensus.fStrictChainId = true;
        consensus.fAllowLegacyBlocks = true;
        consensus.nHeightEffective = 0;

        // Blocks 69360 - 175999 are Digishield without AuxPoW
        digishieldConsensus = consensus;
        digishieldConsensus.nHeightEffective = 69360;
        digishieldConsensus.fSimplifiedRewards = false;
        digishieldConsensus.fDigishieldDifficultyCalculation = true;
        digishieldConsensus.nPowTargetTimespan = 20 * 60; // post-digishield: 20 minute
        digishieldConsensus.nCoinbaseMaturity = 70;

        // Blocks 176000+ are AuxPoW
        auxpowConsensus = digishieldConsensus;
        auxpowConsensus.nHeightEffective = 176000;
        auxpowConsensus.fAllowLegacyBlocks = false;

        // Assemble the binary search tree of consensus parameters
        pConsensusRoot = &digishieldConsensus;
        digishieldConsensus.pLeft = &consensus;
        digishieldConsensus.pRight = &auxpowConsensus;

        /**
         * The message start string is designed to be unlikely to occur in normal data.
         * The characters are rarely used upper ASCII, not valid as UTF-8, and produce
         * a large 32-bit integer with any alignment.
         */
        pchMessageStart[0] = 0xfb;
        pchMessageStart[1] = 0xc0;
        pchMessageStart[2] = 0xb6;
        pchMessageStart[3] = 0xdb;
        nDefaultPort = 9917;
        nPruneAfterHeight = 100000;

        genesis = CreateGenesisBlock(1369199888, 11288888, 0x1e0ffff0, 1, 88 * COIN);

        consensus.hashGenesisBlock = genesis.GetHash();
        digishieldConsensus.hashGenesisBlock = consensus.hashGenesisBlock;
        auxpowConsensus.hashGenesisBlock = consensus.hashGenesisBlock;
        assert(consensus.hashGenesisBlock == uint256S("0x9b7bce58999062b63bfb18586813c42491fa32f4591d8d3043cb4fa9e551541b"));
        assert(genesis.hashMerkleRoot == uint256S("0x6f80efd038566e1e3eab3e1d38131604d06481e77f2462235c6a9a94b1f8abf9"));

        // Note that of those with the service bits flag, most only support a subset of possible options
        vSeeds.push_back(CDNSSeedData("luckycoinfoundation.org", "mainnet.luckycoinfoundation.org", false));

        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,47);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,5);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,175); // 176!
        base58Prefixes[EXT_PUBLIC_KEY] = boost::assign::list_of(0x04)(0x88)(0xB2)(0x1E).convert_to_container<std::vector<unsigned char> >();
        base58Prefixes[EXT_SECRET_KEY] = boost::assign::list_of(0x04)(0x88)(0xAD)(0xE4).convert_to_container<std::vector<unsigned char> >();

        vFixedSeeds = std::vector<SeedSpec6>(pnSeed6_main, pnSeed6_main + ARRAYLEN(pnSeed6_main));

        fMiningRequiresPeers = true;
        fDefaultConsistencyChecks = false;
        fRequireStandard = true;
        fMineBlocksOnDemand = false;

        checkpointData = (CCheckpointData) {
                boost::assign::map_list_of
                        (      0, uint256S("0x9b7bce58999062b63bfb18586813c42491fa32f4591d8d3043cb4fa9e551541b"))
                        (     1, uint256S("0xcf2f78756f0fa64bc4ce80e6d500661cc4c20f2be28c7d859467dceb0adfa2de"))
                        (    53, uint256S("0x9343eae8db94d5d5e945b0c0a6b83647b6a3a8fd89cd170a757e06dcbf2e3bed"))
                        (   117, uint256S("0x5208d62f44467e800a92bfb18fc0fd4c39d9fed28f4ad160262f96dd90111ec3"))
                        (   200, uint256S("0xa5ce00c4aab4f9deccbef0af27adadb29cbf111eb442e92895d7302eb047ad4e"))
                        (  6452, uint256S("0xe502fdfb3a35ee853ccd4a68433b1f9bbe3295c7d453fbcc484d06a766971475"))
                        ( 10978, uint256S("0x88fcee5009a0febf7832750d0246bf4a9b88f8195befc795e5f34b0d1e0e92f9"))
                        ( 17954, uint256S("0x7d40a9b80dd1b585b36e092aefcd3e579ef38f3180ea55dac53ead486f5d9cd2"))
                        ( 23978, uint256S("0x6f111b6eef7dccc2da3c85014964aa402f39c684ba5709b576777503c87141af"))
                        ( 33212, uint256S("0xe3b53359c1b088ec1f772d53eaa765d5c7410f0d9914e69bdb2a0fc881ddc9e8"))
                        ( 45527, uint256S("0x41849cf3bd7b819a6a994d17dcfb1cbc7eadfe63fa61cc1411cfe42177abc06a"))
                        ( 57484, uint256S("0x807fb268c7faabc70cc95c1027cbf1e555834e5bf9e19e01ef785be88853ae88"))
                        ( 69240, uint256S("0x07d2b42e1898d59594b10f26fdc76d4f970a10b4b330237012f48eb489c8d744"))
                        ( 73892, uint256S("0x5b43092ef40969b65878cee7c568e622a4a9d950a130858a10914402797f96b1"))
                        ( 168312, uint256S("0x26816c8861d283ab9bdf4539e5398f65ae5687b90f62cee28036f6e8387933e8"))
                        ( 170421, uint256S("0x647540c0bce26bdcc4f863a6163c1dc86824899835af31cb9d649a85caca38ec"))
                        ( 170924, uint256S("0x28e1a097871c66d25021091fbd68d0f0301d3fc0b106e8d7c6e190e39a20b335"))
                        ( 172330, uint256S("0x8458c3eeda44dc11352edad04e0eb69ae898c69c0dded3b3903b37f5bf352555"))
                        ( 173502, uint256S("0x23bf72398801d9d7cf6d191d06afe49641ec450a8eb960936091bad69d9fb006"))
        };

        chainTxData = ChainTxData{
                // Data as of block ed7d266dcbd8bb8af80f9ccb8deb3e18f9cc3f6972912680feeb37b090f8cee0 (height 4303965).
                // Tx estimate based on average between 2021-07-01 (3793538) and 2022-07-01 (4288126)
                0, // * UNIX timestamp of last checkpoint block
                0,   // * total number of transactions between genesis and last checkpoint
                //   (the tx=... number in the SetBestChain debug.log lines)
                0        // * estimated number of transactions per second after checkpoint
        };
    }
};
static CMainParams mainParams;

/**
 * Testnet (v3)
 */
class CTestNetParams : public CChainParams {
private:
    Consensus::Params digishieldConsensus;
    Consensus::Params auxpowConsensus;
    Consensus::Params minDifficultyConsensus;
public:
    CTestNetParams() {
        strNetworkID = "test";

        consensus.fDigishieldDifficultyCalculation = false;
        consensus.fPowAllowMinDifficultyBlocks = true;
        consensus.fPowAllowDigishieldMinDifficultyBlocks = false;
        consensus.nSubsidyHalvingInterval = 100000;
        consensus.nMajorityEnforceBlockUpgrade = 1500;
        consensus.nMajorityRejectBlockOutdated = 1900;
        consensus.nMajorityWindow = 2000;
        // After deployments are activated we can change it
        consensus.BIP34Height = 0;
        consensus.BIP34Hash = uint256S("0x324635c8e36f663b0adb126a21ad0bd7fa43cc5c5f15aec992bf4dde650bc0ea"); // 0
        consensus.BIP65Height = 0;
        consensus.BIP66Height = 0;
        consensus.powLimit = uint256S("0x00000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"); // ~uint256(0) >> 20;
        consensus.nPowTargetTimespan = 4 * 60 * 60; // pre-digishield: 4 hours
        consensus.nPowTargetSpacing = 60; // 1 minute
        consensus.nCoinbaseMaturity = 70;
        consensus.fPowNoRetargeting = false;
        consensus.nRuleChangeActivationThreshold = 9576; // 95% of 10,080
        consensus.nMinerConfirmationWindow = 10080; // 60 * 24 * 7 = 10,080 blocks, or one week
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = 1199145601; // January 1, 2008
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = 1230767999; // December 31, 2008

        // Deployment of BIP68, BIP112, and BIP113.
        // XXX: BIP heights and hashes all need to be updated to Luckycoin values
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].bit = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nStartTime = 1199145601; // January 1, 2008
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nTimeout = 1230767999; // December 31, 2008

        // Deployment of SegWit (BIP141, BIP143, and BIP147)
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].bit = 1;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nStartTime = 1199145601; // January 1, 2008
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nTimeout = 1230767999; // December 31, 2008

        // The best chain should have at least this much work.
        consensus.nMinimumChainWork = uint256S("0000000000000000000000000000000000000000000000000000000000100010"); // 0

        // By default assume that the signatures in ancestors of this block are valid.
        consensus.defaultAssumeValid = uint256S("0x324635c8e36f663b0adb126a21ad0bd7fa43cc5c5f15aec992bf4dde650bc0ea"); // 0

        // AuxPoW parameters
        consensus.nAuxpowChainId = 0x2013;
        consensus.fStrictChainId = false;
        consensus.nHeightEffective = 0;
        consensus.fAllowLegacyBlocks = true;

        // Blocks 120 - inf are Digishield without minimum difficulty on all blocks
        digishieldConsensus = consensus;
        digishieldConsensus.nHeightEffective = 120;
        digishieldConsensus.nPowTargetTimespan = 20 * 60; // post-digishield: 20 minutes
        digishieldConsensus.fDigishieldDifficultyCalculation = true;
        digishieldConsensus.fSimplifiedRewards = false;
        digishieldConsensus.fPowAllowMinDifficultyBlocks = false;
        digishieldConsensus.nCoinbaseMaturity = 70;

        // Not implementing digishield yet
        minDifficultyConsensus = digishieldConsensus;
        minDifficultyConsensus.nHeightEffective = std::numeric_limits<uint32_t>::max();;
        minDifficultyConsensus.fPowAllowDigishieldMinDifficultyBlocks = true;
        minDifficultyConsensus.fPowAllowMinDifficultyBlocks = true;

        // Not implementing AuxPow hardfork yet
        auxpowConsensus = minDifficultyConsensus;
        auxpowConsensus.nHeightEffective = std::numeric_limits<uint32_t>::max();
        auxpowConsensus.fPowAllowDigishieldMinDifficultyBlocks = true;
        auxpowConsensus.fAllowLegacyBlocks = false;

        // Assemble the binary search tree of parameters
        pConsensusRoot = &digishieldConsensus;
        digishieldConsensus.pLeft = &consensus;
        digishieldConsensus.pRight = &minDifficultyConsensus;
        minDifficultyConsensus.pRight = &auxpowConsensus;

        pchMessageStart[0] = 0xfc;
        pchMessageStart[1] = 0xc1;
        pchMessageStart[2] = 0xb7;
        pchMessageStart[3] = 0xdc;
        nDefaultPort = 19917;
        nPruneAfterHeight = 100000;

        genesis = CreateGenesisBlock(1369199888, 12097647, 0x1e0ffff0, 1, 88 * COIN);
        consensus.hashGenesisBlock = genesis.GetHash();
        digishieldConsensus.hashGenesisBlock = consensus.hashGenesisBlock;
        minDifficultyConsensus.hashGenesisBlock = consensus.hashGenesisBlock;
        auxpowConsensus.hashGenesisBlock = consensus.hashGenesisBlock;
        assert(consensus.hashGenesisBlock == uint256S("0x324635c8e36f663b0adb126a21ad0bd7fa43cc5c5f15aec992bf4dde650bc0ea"));
        assert(genesis.hashMerkleRoot == uint256S("0x6f80efd038566e1e3eab3e1d38131604d06481e77f2462235c6a9a94b1f8abf9"));

        // nodes with support for servicebits filtering should be at the top
        vSeeds.push_back(CDNSSeedData("luckycoinfoundation.org", "testnet.luckycoinfoundation.org", false));

        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,113);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,196);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,241); //153
        base58Prefixes[EXT_PUBLIC_KEY] = boost::assign::list_of(0x04)(0x35)(0x87)(0xCF).convert_to_container<std::vector<unsigned char> >();
        base58Prefixes[EXT_SECRET_KEY] = boost::assign::list_of(0x04)(0x35)(0x83)(0x94).convert_to_container<std::vector<unsigned char> >();

        vFixedSeeds = std::vector<SeedSpec6>(pnSeed6_test, pnSeed6_test + ARRAYLEN(pnSeed6_test));

        fMiningRequiresPeers = true;
        fDefaultConsistencyChecks = false;
        fRequireStandard = false;
        fMineBlocksOnDemand = false;

        checkpointData = (CCheckpointData) {
                boost::assign::map_list_of
                        (      0, uint256S("0x324635c8e36f663b0adb126a21ad0bd7fa43cc5c5f15aec992bf4dde650bc0ea"))
        };

        chainTxData = ChainTxData{
                // Data as of block 0x324635c8e36f663b0adb126a21ad0bd7fa43cc5c5f15aec992bf4dde650bc0ea (height 0).
                // Tx estimate based on average between 2021-07-01 (3793538) and 2022-07-01 (4288126)
                0, // * UNIX timestamp of last checkpoint block
                0,   // * total number of transactions between genesis and last checkpoint
                //   (the tx=... number in the SetBestChain debug.log lines)
                0        // * estimated number of transactions per second after checkpoint
        };

    }
};
static CTestNetParams testNetParams;

/**
 * Regression test
 */
class CRegTestParams : public CChainParams {
private:
    Consensus::Params digishieldConsensus;
    Consensus::Params auxpowConsensus;
public:
    CRegTestParams() {
        strNetworkID = "regtest";

        consensus.nSubsidyHalvingInterval = 100000;
        consensus.nMajorityEnforceBlockUpgrade = 1500;
        consensus.nMajorityRejectBlockOutdated = 1900;
        consensus.nMajorityWindow = 2000;
        consensus.BIP34Height = 0;
        consensus.BIP34Hash = uint256S("0x324635c8e36f663b0adb126a21ad0bd7fa43cc5c5f15aec992bf4dde650bc0ea"); // 0
        consensus.BIP65Height = 0;
        consensus.BIP66Height = 0;
        consensus.powLimit = uint256S("0x00000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"); // ~uint256(0) >> 20;
        consensus.nPowTargetTimespan = 4 * 60 * 60; // pre-digishield: 4 hours
        consensus.nPowTargetSpacing = 20 * 60; // 20 minutes
        consensus.fDigishieldDifficultyCalculation = false;
        consensus.fPowAllowMinDifficultyBlocks = true;
        consensus.fPowNoRetargeting = true;
        consensus.nRuleChangeActivationThreshold = 9576; // 95% of 10,080
        consensus.nMinerConfirmationWindow = 10080; // 60 * 24 * 7 = 10,080 blocks, or one week
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].bit = 28;
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nStartTime = 1199145601; // January 1, 2008
        consensus.vDeployments[Consensus::DEPLOYMENT_TESTDUMMY].nTimeout = 1230767999; // December 31, 2008

        // Deployment of BIP68, BIP112, and BIP113.
        // XXX: BIP heights and hashes all need to be updated to Luckycoin values
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].bit = 0;
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nStartTime = 1199145601; // January 1, 2008
        consensus.vDeployments[Consensus::DEPLOYMENT_CSV].nTimeout = 1230767999; // December 31, 2008

        // Deployment of SegWit (BIP141, BIP143, and BIP147)
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].bit = 1;
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nStartTime = 1199145601; // January 1, 2008
        consensus.vDeployments[Consensus::DEPLOYMENT_SEGWIT].nTimeout = 1230767999; // December 31, 2008

        // The best chain should have at least this much work.
        consensus.nMinimumChainWork = uint256S("0000000000000000000000000000000000000000000000000000000000100010"); // 0

        // By default assume that the signatures in ancestors of this block are valid.
        consensus.defaultAssumeValid = uint256S("0x324635c8e36f663b0adb126a21ad0bd7fa43cc5c5f15aec992bf4dde650bc0ea"); // 0

        // AuxPow parameters
        consensus.nAuxpowChainId = 0x2013;
        consensus.fStrictChainId = true;
        consensus.fAllowLegacyBlocks = true;

        // Luckycoin parameters
        consensus.fSimplifiedRewards = false;
        consensus.nCoinbaseMaturity = 70; // For easier testability in RPC tests
		consensus.nHeightEffective = 0;

        digishieldConsensus = consensus;
        digishieldConsensus.nHeightEffective = 120;
        digishieldConsensus.nPowTargetTimespan = 20 * 60; // post-digishield: 20 minutes
        digishieldConsensus.fDigishieldDifficultyCalculation = true;

        auxpowConsensus = digishieldConsensus;
        auxpowConsensus.fAllowLegacyBlocks = false;
        auxpowConsensus.nHeightEffective = 240;

        // Assemble the binary search tree of parameters
        digishieldConsensus.pLeft = &consensus;
        digishieldConsensus.pRight = &auxpowConsensus;
        pConsensusRoot = &digishieldConsensus;

        pchMessageStart[0] = 0xc0;
        pchMessageStart[1] = 0xc0;
        pchMessageStart[2] = 0xc0;
        pchMessageStart[3] = 0xc0;
        nDefaultPort = 29917;
        nPruneAfterHeight = 100000;

        genesis = CreateGenesisBlock(1369199888, 12097647, 0x1e0ffff0, 1, 88 * COIN);
        consensus.hashGenesisBlock = genesis.GetHash();
        digishieldConsensus.hashGenesisBlock = consensus.hashGenesisBlock;
        auxpowConsensus.hashGenesisBlock = consensus.hashGenesisBlock;
        assert(consensus.hashGenesisBlock == uint256S("0x324635c8e36f663b0adb126a21ad0bd7fa43cc5c5f15aec992bf4dde650bc0ea"));
        assert(genesis.hashMerkleRoot == uint256S("0x6f80efd038566e1e3eab3e1d38131604d06481e77f2462235c6a9a94b1f8abf9"));

        // nodes with support for servicebits filtering should be at the top

        base58Prefixes[PUBKEY_ADDRESS] = std::vector<unsigned char>(1,113);
        base58Prefixes[SCRIPT_ADDRESS] = std::vector<unsigned char>(1,196);
        base58Prefixes[SECRET_KEY] =     std::vector<unsigned char>(1,241); // 153
        base58Prefixes[EXT_PUBLIC_KEY] = boost::assign::list_of(0x04)(0x35)(0x87)(0xCF).convert_to_container<std::vector<unsigned char> >();
        base58Prefixes[EXT_SECRET_KEY] = boost::assign::list_of(0x04)(0x35)(0x83)(0x94).convert_to_container<std::vector<unsigned char> >();

        vFixedSeeds = std::vector<SeedSpec6>(pnSeed6_main, pnSeed6_main + ARRAYLEN(pnSeed6_main));

        fMiningRequiresPeers = false;
        fDefaultConsistencyChecks = true;
        fRequireStandard = false;
        fMineBlocksOnDemand = true;

        checkpointData = (CCheckpointData){
                boost::assign::map_list_of
                        ( 0, uint256S("0x324635c8e36f663b0adb126a21ad0bd7fa43cc5c5f15aec992bf4dde650bc0ea"))
        };

        chainTxData = ChainTxData{
                0,
                0,
                0
        };
    }

    void UpdateBIP9Parameters(Consensus::DeploymentPos d, int64_t nStartTime, int64_t nTimeout)
    {
        consensus.vDeployments[d].nStartTime = nStartTime;
        consensus.vDeployments[d].nTimeout = nTimeout;
    }
};
static CRegTestParams regTestParams;

static CChainParams *pCurrentParams = 0;

const CChainParams &Params() {
    assert(pCurrentParams);
    return *pCurrentParams;
}

const Consensus::Params *Consensus::Params::GetConsensus(uint32_t nTargetHeight) const {
    if (nTargetHeight < this -> nHeightEffective && this -> pLeft != NULL) {
        return this -> pLeft -> GetConsensus(nTargetHeight);
    } else if (nTargetHeight > this -> nHeightEffective && this -> pRight != NULL) {
        const Consensus::Params *pCandidate = this -> pRight -> GetConsensus(nTargetHeight);
        if (pCandidate->nHeightEffective <= nTargetHeight) {
            return pCandidate;
        }
    }

    // No better match below the target height
    return this;
}

CChainParams& Params(const std::string& chain)
{
    if (chain == CBaseChainParams::MAIN)
            return mainParams;
    else if (chain == CBaseChainParams::TESTNET)
            return testNetParams;
    else if (chain == CBaseChainParams::REGTEST)
            return regTestParams;
    else
        throw std::runtime_error(strprintf("%s: Unknown chain %s.", __func__, chain));
}

void SelectParams(const std::string& network)
{
    SelectBaseParams(network);
    pCurrentParams = &Params(network);
}

void UpdateRegtestBIP9Parameters(Consensus::DeploymentPos d, int64_t nStartTime, int64_t nTimeout)
{
    regTestParams.UpdateBIP9Parameters(d, nStartTime, nTimeout);
}
