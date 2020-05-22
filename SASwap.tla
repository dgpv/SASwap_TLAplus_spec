-------------------------------- MODULE SASwap ---------------------------------
\* `.SASwap TLA+ specification (c) by Dmitry Petukhov (https://github.com/dgpv)
\* `.Licensed under a Creative Commons Attribution-ShareAlike 4.0 International
\* `.License <http://creativecommons.org/licenses/by-sa/4.0/>

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT ALICE_IRRATIONAL \* Can alice act irrational ?
ASSUME ALICE_IRRATIONAL \in BOOLEAN

CONSTANT BLOCKS_PER_DAY
ASSUME BLOCKS_PER_DAY >= 1

\* A transaction that has no deadline can be 'stalling',
\* i.e. not being sent while being enabled, for this number of days
CONSTANT MAX_DAYS_STALLING
ASSUME MAX_DAYS_STALLING >= 1

CONSTANT STEALTHY_SEND_POSSIBLE
ASSUME STEALTHY_SEND_POSSIBLE \in BOOLEAN

Range(f) == { f[x] : x \in DOMAIN f }
Min(set) == CHOOSE x \in set: \A y \in set : x <= y
Max(set) == CHOOSE x \in set: \A y \in set : x >= y

Tx(id, ss, ds, by, to, via) ==
    [ id |-> id, ss |-> ss, ds |-> ds, to |-> to, by |-> by, via |-> via ]

VARIABLE blocks            \* <<{Tx, ...}, ...>>
VARIABLE next_block        \* {Tx, ...}
VARIABLE mempool           \* {Tx, ...}
VARIABLE shared_knowledge  \* {Tx, ...}
VARIABLE signers_map       \* [participant |-> {allowed_sig, ...}]
VARIABLE per_block_enabled \* <<{Tx, ...}, ...>>

fullState  == <<blocks, next_block, signers_map, shared_knowledge, mempool, per_block_enabled>>
allExceptNextBlock  == <<blocks, signers_map, shared_knowledge, mempool>>

\* Various definitions that help to improve readability of the spec

Alice == "Alice"
Bob   == "Bob"
participants == { Alice, Bob }

sigAlice    == "sigAlice"
sigBob      == "sigBob"
secretAlice == "secretAlice"
secretBob   == "secretBob"
all_secrets == { secretAlice, secretBob }
all_sigs    == { sigAlice, sigBob, secretAlice, secretBob }

tx_lock_A               == "tx_lock_A"
tx_lock_B               == "tx_lock_B"
tx_success              == "tx_success"
tx_refund_1             == "tx_refund_1"
tx_revoke               == "tx_revoke"
tx_refund_2             == "tx_refund_2"
tx_timeout              == "tx_timeout"
tx_spend_A              == "tx_spend_A"
tx_spend_B              == "tx_spend_B"
tx_spend_success        == "tx_spend_success"
tx_spend_refund_1_alice == "tx_spend_refund_1_alice"
tx_spend_refund_1_bob   == "tx_spend_refund_1_bob"
tx_spend_revoke         == "tx_spend_revoke"
tx_spend_refund_2       == "tx_spend_refund_2"
tx_spend_timeout        == "tx_spend_timeout"

nLockTime == "nLockTime"
nSequence == "nSequence"
NoTimelock == [ days |-> 0, type |-> nLockTime ]

\* If blocks per day are low, the absolute locks
\* need to be shifted for all contract paths to be reachable
ABS_LK_OFFSET == CASE BLOCKS_PER_DAY = 1 -> 2
                   [] BLOCKS_PER_DAY = 2 -> 1
                   [] OTHER              -> 0

\* The map of the transactions, their possible destinations and timelocks.

\* Adaptor signatures are modelled by an additional value in the required signature set.
\* For modelling purposes, the secret acts as just another sig.

\* Note: `ds' stands for "destinations", `ss' for "signatures", `lk' for "lock"

tx_map == [

    \* 'Contract' transactions -- destinations are other transactions

    \* XXX items need not be sets now

    tx_lock_A   |-> {[ds |-> { tx_success, tx_refund_1, tx_revoke, tx_spend_A },
                      ss |-> { sigAlice }]},

    tx_lock_B   |-> {[ds |-> { tx_spend_B },
                      ss |-> { sigBob }]},

    tx_success  |-> {[ds |-> { tx_spend_success },
                      ss |-> { sigAlice, sigBob, secretBob }]},

    tx_refund_1 |-> {[ds |-> { tx_spend_refund_1_bob, tx_spend_refund_1_alice },
                      ss |-> { sigAlice, sigBob, secretAlice },
                      lk |-> [ days |-> ABS_LK_OFFSET + 1, type |-> nLockTime ]]},

    tx_revoke   |-> {[ds |-> { tx_refund_2, tx_timeout, tx_spend_revoke },
                      ss |-> { sigAlice, sigBob },
                      lk |-> [ days |-> ABS_LK_OFFSET + 2, type |-> nLockTime ]]},

    tx_refund_2 |-> {[ds |-> { tx_spend_refund_2 },
                      ss |-> { sigAlice, sigBob, secretAlice },
                      lk |-> [ days |-> 1, type |-> nSequence ]]},

    tx_timeout  |-> {[ds |-> { tx_spend_timeout },
                      ss |-> { sigAlice, sigBob },
                      lk |-> [ days |-> 2, type |-> nSequence ]]},

    \* `^\newpage^'
    \* 'Terminal' transactions -- destinations are participants

    tx_spend_A        |-> {[ds |-> { Alice, Bob },
                            ss |-> { sigAlice, sigBob }]},

    tx_spend_B        |-> {[ds |-> { Alice, Bob },
                            ss |-> { secretAlice, secretBob }]},

    tx_spend_success  |-> {[ds |-> { Bob },
                            ss |-> { sigBob }]},

    tx_spend_refund_1_bob
                      |-> {[ds |-> { Bob },
                            ss |-> { sigAlice, sigBob }]},

    tx_spend_refund_1_alice
                      |-> {[ds |-> { Alice },
                            ss |-> { sigAlice },
                            lk |-> [ days |-> 1, type |-> nSequence ]]},

    tx_spend_revoke   |-> {[ds |-> { Alice, Bob },
                            ss |-> { sigAlice, sigBob }]},

    tx_spend_refund_2 |-> {[ds |-> { Alice },
                            ss |-> { sigAlice }]},

    tx_spend_timeout  |-> {[ds |-> { Bob },
                            ss |-> { sigBob }]}
]

all_transactions == DOMAIN tx_map

\* No variants for transaction with identical destination sets are allowed,
\* because we use (id, ds) to identify a transaction variant
ASSUME \A vset \in Range(tx_map):
            Cardinality({ v["ds"]: v \in vset }) = Cardinality(vset)

\* On-chain, contract starts with Alice locking A
first_transaction == tx_lock_A

\* This will fail if there's more than one variant
SoleVariant(id) == CHOOSE v \in tx_map[id]: Cardinality(tx_map[id]) = 1

ConfirmedTransactions == { tx.id: tx \in UNION Range(blocks) }

NextBlockTransactions == { tx.id: tx \in next_block }

NextBlockConfirmedTransactions ==
    ConfirmedTransactions \union NextBlockTransactions

MempoolTransactions == { tx.id: tx \in mempool }

SentTransactions == ConfirmedTransactions \union MempoolTransactions

ContractTransactions ==
    { id \in all_transactions:
         \A variant \in tx_map[id]:
         \A d \in variant.ds: d \in all_transactions }

TerminalTransactions ==
    { id \in all_transactions:
         \A variant \in tx_map[id]:
         \A d \in variant.ds: d \in participants }

ASSUME \A id \in all_transactions: \/ id \in TerminalTransactions
                                   \/ id \in ContractTransactions

\* In this contract each transaction has only one parent,
\* so we can use simple mapping from dep_id to parent id
dependency_map ==
    [ dep_id \in
         UNION { v.ds: v \in UNION { tx_map[id]: id \in ContractTransactions } }
      |-> CHOOSE id \in ContractTransactions:
             dep_id \in UNION { v.ds: v \in tx_map[id] } ]

\* Special destination for the case when funds will still be locked
\* at the contract after the transaction is spent
Contract == "Contract"

DstSet(id, ds) == IF id \in ContractTransactions THEN { Contract } ELSE ds

ConflictingSet(id) ==
    IF id \in DOMAIN dependency_map
    THEN { dep_id \in DOMAIN dependency_map:
           dependency_map[dep_id] = dependency_map[id] }
    ELSE { id }

\* Transaction also conflicts with itself
ASSUME \A id \in all_transactions: id \in ConflictingSet(id)

ConfirmationHeight(id) ==
    CHOOSE bn \in DOMAIN blocks: \E tx \in blocks[bn]: tx.id = id

RECURSIVE DependencyChain(_)
DependencyChain(id) ==
    IF id \in DOMAIN dependency_map
    THEN { id } \union DependencyChain(dependency_map[id])
    ELSE { id }

RECURSIVE AllDependants(_)
AllDependants(id) ==
    LET dependants == (UNION { v.ds: v \in tx_map[id] }) \ participants
     IN IF dependants = {}
        THEN { id }
        ELSE dependants \union UNION { AllDependants(d_id): d_id \in dependants }

InvalidatedTransactions ==
    UNION { { c_id } \union AllDependants(c_id): c_id \in
            UNION { ConflictingSet(id) \ { id }: id \in ConfirmedTransactions } }

RemainingTransactions ==
    ((all_transactions \ ConfirmedTransactions) \ InvalidatedTransactions)

Timelock(id, ds) ==
    LET v == CHOOSE v \in tx_map[id]: v.ds = ds
     IN IF "lk" \in DOMAIN v
        THEN v.lk
        ELSE NoTimelock

\* Transaction variants with different timelock types are not modelled
ASSUME \A id \in all_transactions:
       \A v1 \in tx_map[id]:
       \A v2 \in tx_map[id]:
            LET t1 == Timelock(id, v1.ds)
                t2 == Timelock(id, v2.ds)
             IN t1.type = t2.type \/ NoTimelock \in { t1, t2 }

UnreachableHeight == 2^30+(2^30-1)

TimelockExpirationHeight(id, ds) ==
    LET lk == Timelock(id, ds)
     IN CASE lk.type = nLockTime
             -> lk.days * BLOCKS_PER_DAY
          [] lk.type = nSequence
              -> IF dependency_map[id] \in ConfirmedTransactions
                 THEN ConfirmationHeight(dependency_map[id])
                      + lk.days * BLOCKS_PER_DAY
                 ELSE UnreachableHeight

\* "Hard" deadline for transaction means that it is unsafe to publish
\* the transaction after the deadline
Deadline(id, ds) ==
    LET hs == UNION { { TimelockExpirationHeight(c_id, v.ds): v \in tx_map[c_id] }:
                      c_id \in ConflictingSet(id) \ { id } }
        higher_hs == { h \in hs: h > TimelockExpirationHeight(id, ds) }
     IN IF higher_hs = {}
        THEN UnreachableHeight
        ELSE Min(higher_hs)

\* "Soft" deadline for transaction means that after the deadline,
\* mining the transaction will mean that it was 'stalling' for too long
SoftDeadline(id, ds) ==
    LET dl == Deadline(id, ds)
        h == TimelockExpirationHeight(id, ds)
     IN IF dl = UnreachableHeight
        THEN IF \E tx \in UNION Range(per_block_enabled): tx.id = id /\ tx.ds = ds
             THEN ( CHOOSE en \in DOMAIN per_block_enabled:
                        \E tx \in per_block_enabled[en]: tx.id = id /\ tx.ds = ds )
                  + MAX_DAYS_STALLING * BLOCKS_PER_DAY
             ELSE IF h /= UnreachableHeight
                  THEN h + MAX_DAYS_STALLING * BLOCKS_PER_DAY
                  ELSE 0
        ELSE dl

SigsAvailable(id, ds, sender, to) ==
    LET secrets_shared ==
            UNION { tx.ss \intersect all_secrets: tx \in shared_knowledge }
        sigs_shared ==
            UNION { tx.ss: tx \in { tx \in shared_knowledge: /\ tx.id = id
                                                             /\ tx.ds = ds
                                                             /\ tx.to = to } }
     IN sigs_shared \union secrets_shared \union signers_map[sender]

DependencySatisfied(id, ids) ==
    id \in DOMAIN dependency_map => dependency_map[id] \in ids

IsSpendableTx(tx, other_ids) ==
    /\ {} = ConflictingSet(tx.id) \intersect other_ids
    /\ DependencySatisfied(tx.id, other_ids)
    /\ tx.ss \subseteq SigsAvailable(tx.id, tx.ds, tx.by, tx.to)
    /\ Len(blocks) >= TimelockExpirationHeight(tx.id, tx.ds)

\* Sending tx_spend_B does not actually expose secrets, because the secrets
\* are used as keys, and sigSecretBob would be exposed rather than secretBob.
\* Instead of introducing revealSecret<Alice|Bob>, sigSecret<Alice|Bob>
\* we simply filter out signatures of tx_spend_B before placing into shared knowledge
ShareKnowledge(knowledge) ==
    LET knowledge_filtered ==
            { IF tx.id /= tx_spend_B THEN tx ELSE [tx EXCEPT !.ss = {}]:
              tx \in knowledge }
        \* shared_knowledge may not change here, callers need to check if they care
     IN shared_knowledge' = shared_knowledge \union knowledge_filtered

ShareTransactions(ids, by) ==
    LET Dst(id) == IF id \in ContractTransactions
                   THEN Contract
                   ELSE LET v == CHOOSE v \in tx_map[id]: TRUE
                        IN CASE Cardinality(v.ds) = 1 -> CHOOSE d \in v.ds: TRUE
                        \* no 'OTHER' clause - no sharing of ambigous-dst transactions
        Ss(v) == (v.ss \intersect signers_map[by]) \ all_secrets
        txs == UNION { { Tx(id, Ss(v), v.ds, by, Dst(id), "direct"): v \in tx_map[id] }:
                       id \in ids }
     IN /\ ShareKnowledge(txs)
        /\ shared_knowledge' /= shared_knowledge \* not a new knowledge => fail

\* Txs enabled at the current cycle, used to update per_block_enabled vector
NewlyEnabledTxs ==
    { tx \in
      UNION
      { UNION
        { UNION
          {
            {
              Tx(id, variant.ss, variant.ds, sender, to, "enabled"):
              to \in DstSet(id, variant.ds)
            }: variant \in tx_map[id]
          }: id \in RemainingTransactions
        }: sender \in participants
      }: /\ ~\E etx \in UNION Range(per_block_enabled):
                etx.id = tx.id /\ etx.ds = tx.ds
         /\ IsSpendableTx(tx, ConfirmedTransactions)
    }

SendTransactionToMempool(id, variant, sender, to) ==
    LET tx == Tx(id, variant.ss, variant.ds, sender, to, "mempool")
     IN /\ IsSpendableTx(tx, SentTransactions)
        /\ Len(blocks) < Deadline(id, variant.ds)
        /\ mempool' = mempool \union { tx }
        /\ ShareKnowledge({ tx })

\* Give tx directly to miner, bypassing global mempool
\* No Deadline check because information is not shared,
\* and after the block is mined, there's no possible contention
\* unless the block is orphaned. Orphan blocks are not modelled,
\* and therefore there's no need for additional restriction
\* as any state space restriction can possibly mask some other issue
SendTransactionToMiner(id, variant, sender, to) ==
    /\ STEALTHY_SEND_POSSIBLE
    /\ LET tx == Tx(id, variant.ss, variant.ds, sender, to, "miner")
       IN /\ IsSpendableTx(tx, NextBlockConfirmedTransactions)
          /\ next_block' = next_block \union { tx }

SendTransaction(id, variant, sender, to) ==
    \/ /\ SendTransactionToMempool(id, variant, sender, to)
       /\ UNCHANGED next_block
    \/ /\ SendTransactionToMiner(id, variant, sender, to)
       /\ UNCHANGED <<mempool, shared_knowledge>>

SendSomeTransaction(ids, sender) ==
    \E id \in ids:
    \E variant \in tx_map[id]:
    \E to \in DstSet(id, variant.ds \intersect { sender }):
        SendTransaction(id, variant, sender, to)

HasCustody(ids, participant) ==
    \E id \in ids: \E tx \in UNION Range(blocks): tx.id = id /\ tx.to = participant

\* Sharing secrets or keys has to occur before deadline to send tx_success
TooLateToShare == Len(blocks) >= Deadline(tx_success, SoleVariant(tx_success).ds)

(***********************)
(* Participant actions *)
(***********************)

\* Transactions Alice initially shares signatures on
phase0_to_share_Alice == { tx_revoke, tx_timeout }

\* Transactions Bob initially shares signatures on
phase0_to_share_Bob == { tx_refund_1, tx_revoke, tx_refund_2, tx_timeout }

\* Conditions to divide the contract execution into phases according to original spec

Phase_3_cond == tx_lock_B \in ConfirmedTransactions
Phase_2_cond == tx_lock_A \in ConfirmedTransactions
Phase_1_cond ==
    /\ \A id \in phase0_to_share_Alice:
           \E tx \in shared_knowledge: tx.id = id /\ sigAlice \in tx.ss
    /\ \A id \in phase0_to_share_Bob:
           \E tx \in shared_knowledge: tx.id = id /\ sigBob \in tx.ss

InPhase_3 ==
    /\ Phase_3_cond

InPhase_2 ==
    /\ Phase_2_cond
    /\ ~Phase_3_cond

InPhase_1 ==
    /\ Phase_1_cond
    /\ ~Phase_2_cond
    /\ ~Phase_3_cond

InPhase_0 ==
    /\ ~Phase_1_cond
    /\ ~Phase_2_cond
    /\ ~Phase_3_cond

\* Helper operators to declutter the action expressions
NoSending == UNCHANGED <<mempool, next_block>>
NoKeysShared == UNCHANGED signers_map
NoKnowledgeShared == UNCHANGED shared_knowledge

\* `^\newpage^'

AliceAction ==
    LET Send(ids) == SendSomeTransaction(ids, Alice)
        Share(ids) == ShareTransactions(ids, Alice)
        SafeToSend(id) ==
            CASE ALICE_IRRATIONAL -> TRUE \* Unsafe txs are OK for irrational Alice
              [] id = tx_refund_1 \* Do not send refund_1 if tx_success was shared
                 -> tx_success \notin { tx.id: tx \in shared_knowledge }
              [] secretAlice \in UNION { v.ss: v \in tx_map[id] }
                 \* Once Alice received secretBob, should never send out secretAlice
                 -> \/ secretBob \notin signers_map[Alice]
                    \/ id = tx_spend_B \* unless this is a transaction to get B
                                       \* which does not in fact expose secrets
              [] OTHER -> TRUE
     IN \/ /\ InPhase_0
           /\ Share(phase0_to_share_Alice)
           /\ NoSending /\ NoKeysShared
        \/ /\ InPhase_1
           /\ Send({ tx_lock_A })
           /\ NoKeysShared
        \/ /\ InPhase_2 \* Just waiting for Bob to lock B
           /\ NoSending /\ NoKnowledgeShared /\ NoKeysShared
        \/ /\ InPhase_3
           /\ \/ /\ secretBob \in signers_map[Alice] \* Bob gave Alice his secret
                 /\ sigAlice \notin signers_map[Bob] \* Alice did not yet gave Bob her key
                 /\ ~TooLateToShare
                 /\ signers_map' = [signers_map  \* Give Alice's key to Bob
                                    EXCEPT ![Bob] = @ \union { sigAlice }]
                 /\ NoSending /\ NoKnowledgeShared
              \/ /\ tx_refund_1 \notin SentTransactions
                 /\ ~TooLateToShare
                 /\ Share({ tx_success }) \* refund_1 not sent yet, can share
                 /\ NoSending /\ NoKeysShared
              \/ /\ Send({ id \in RemainingTransactions: SafeToSend(id) })
                 /\ NoKeysShared

\* `^\newpage^'

BobAction ==
    LET Send(ids) == SendSomeTransaction(ids, Bob)
        Share(ids) == ShareTransactions(ids, Bob)
        tx_success_sigs == \* To check that signed tx_success was shared by Alice
            SigsAvailable(tx_success, SoleVariant(tx_success).ds, Bob, Contract)
     IN \/ /\ InPhase_0
           /\ Share(phase0_to_share_Bob)
           /\ NoSending /\ NoKeysShared
        \/ /\ InPhase_1 \* Just waiting for Alice to lock A
           /\ NoSending /\ NoKnowledgeShared /\ NoKeysShared
        \/ /\ \/ InPhase_2
              \/ InPhase_3
           /\ \/ /\ sigAlice \in tx_success_sigs
                    \* If Bob already knows secretAlice, he doesn't need to share secretBob
                 /\ secretAlice \notin tx_success_sigs
                 /\ secretBob \notin signers_map[Alice]
                 /\ ~TooLateToShare
                 /\ signers_map' = [signers_map \* Give secretBob to Alice
                                    EXCEPT ![Alice] = @ \union { secretBob }]
                 /\ NoSending /\ NoKnowledgeShared
              \/ /\ Send(RemainingTransactions)
                 /\ NoKeysShared

\*`^\newpage^'

MempoolMonitorActionRequired ==
    \E tx \in mempool: /\ Len(blocks) + 1 = Deadline(tx.id, tx.ds)
                       /\ tx.id \notin NextBlockTransactions

\* We update next_block directly rather than having to deal with fees and prioritization.
\* What we want to model is the behavior of participants where once they have sent
\* the transaction, they do anything possible to meet the deadline set by the protocol
\* to confirm the transaction. Failure to do so before the deadline is out of scope,
\* even though it could be caused by some unexpected mempool behavior.

\* Exact mempool behavior is too low-level and is better modelled separately to check that
\* high-level constraints can be met. Although if we were to have more complex model where
\* the amounts available for each participant are tracked, it might make sense to include
\* the fees and mempool behavior into the model of the contract to catch the cases
\* when participants just can't bump fees anymore, for example.

\* We could just not model the mempool monitoring, and constrain state space such that
\* states with late txs are invalid, to express that we don't care about the cases when
\* participants fail to get their txs confirmed in time. But maybe there could be some
\* interesting behaviors to be modelled if more elaborate monitor action is implemented

MempoolMonitorAction ==
    LET tx == CHOOSE tx \in mempool: Len(blocks) + 1 = Deadline(tx.id, tx.ds)
        txs_to_bump == { tx } \union { dptx \in mempool:
                                      /\ tx.id \in DOMAIN dependency_map
                                      /\ dptx.id = dependency_map[tx.id]
                                      /\ dptx.id \notin NextBlockTransactions }
     IN next_block' =
            { nbtx \in next_block: \* conflicting txs are expunged from next_block
              {} = DependencyChain(nbtx.id) \intersect
                     UNION { ConflictingSet(bmptx.id): bmptx \in txs_to_bump } }
            \union { [bmptx EXCEPT !.via = "fee-bump"]: bmptx \in txs_to_bump }

\*`^\newpage^'

(****************)
(* Miner action *)
(****************)

IncludeTxIntoBlock ==
    /\ \E tx \in mempool:
          /\ {} = ConflictingSet(tx.id) \intersect NextBlockConfirmedTransactions
          /\ DependencySatisfied(tx.id, NextBlockConfirmedTransactions)
          /\ next_block' = next_block \union { tx }
    /\ UNCHANGED <<blocks, mempool, shared_knowledge>>

CanMineEmptyBlock ==
    /\ first_transaction \in ConfirmedTransactions
    /\ LET soft_dls == UNION { { SoftDeadline(id, v.ds): v \in tx_map[id] }:
                               id \in RemainingTransactions }
        IN soft_dls /= {} /\ Len(blocks) + 1 < Max(soft_dls)

MineTheBlock ==
    IF next_block = {}
    THEN /\ CanMineEmptyBlock
         /\ blocks' = Append(blocks, {})
         /\ UNCHANGED <<mempool, next_block, shared_knowledge>>
    ELSE /\ blocks' = Append(blocks, next_block)
         /\ mempool' =
              { tx \in mempool: \* conflicting txs are expunged from mempool
                {} = DependencyChain(tx.id) \intersect
                     UNION { ConflictingSet(nbtx.id): nbtx \in next_block } }
         /\ next_block' = {}
         /\ ShareKnowledge(next_block \ mempool)

MinerAction == IncludeTxIntoBlock \/ MineTheBlock

(***********************************************)
(* Auxiliary action for soft-deadline tracking *)
(***********************************************)

UpdateEnabledPerBlock ==
    per_block_enabled' =
        IF Len(per_block_enabled) < Len(blocks) + 1
        THEN Append(per_block_enabled, NewlyEnabledTxs)
        ELSE [per_block_enabled EXCEPT ![Len(blocks) + 1] = @ \union NewlyEnabledTxs]

(****************************)
(* High-level contract spec *)
(****************************)

SwapSuccessful ==
    /\ HasCustody({ tx_spend_B }, Alice)
    /\ \/ HasCustody({ tx_spend_A, tx_spend_success,
                       tx_spend_timeout, tx_spend_revoke }, Bob)
       \/ /\ ALICE_IRRATIONAL
          /\ HasCustody({ tx_spend_refund_1_bob }, Bob)

SwapAborted ==
    /\ HasCustody({ tx_spend_A, tx_spend_refund_1_alice, tx_spend_refund_2 }, Alice)
    /\ HasCustody({ tx_spend_B }, Bob)

SwapTimedOut ==
    /\ tx_spend_timeout \in ConfirmedTransactions
       \* Alice can't claim tx_spend_B on timeout
    /\ secretBob \notin signers_map[Alice]
    /\ secretBob \notin UNION { tx.ss: tx \in shared_knowledge }

AliceLostByMisbehaving ==
    /\ HasCustody({ tx_spend_B }, Bob)
    /\ HasCustody({ tx_spend_refund_1_bob }, Bob)

BobLostByBeingLateOnRefund_1 ==
    /\ HasCustody({ tx_spend_B }, Alice)
    /\ HasCustody({ tx_spend_refund_1_alice }, Alice)

BobLostByBeingLateOnRefund_2 ==
    /\ HasCustody({ tx_spend_B }, Alice)
    /\ HasCustody({ tx_spend_refund_2 }, Alice)

SwapUnnaturalEnding ==
    /\ ALICE_IRRATIONAL
    /\ \/ AliceLostByMisbehaving
       \/ BobLostByBeingLateOnRefund_1
       \/ BobLostByBeingLateOnRefund_2

ContractFinished == \/ SwapSuccessful
                    \/ SwapAborted
                    \/ SwapTimedOut
                    \/ SwapUnnaturalEnding

ContractAction ==
    \/ AliceAction               /\ UNCHANGED blocks
    \/ BobAction                 /\ UNCHANGED blocks
    \/ IF MempoolMonitorActionRequired
       THEN MempoolMonitorAction /\ UNCHANGED allExceptNextBlock
       ELSE MinerAction          /\ UNCHANGED signers_map

\*`^\newpage^'
(***************)
(* Invariants  *)
(***************)

TypeOK ==
    LET TxConsistent(tx, vias) ==
            /\ tx.id \in all_transactions
            /\ tx.ss \subseteq UNION { v.ss: v \in tx_map[tx.id] }
            /\ tx.ds \in { v.ds: v \in tx_map[tx.id] }
            /\ tx.to \in UNION { DstSet(tx.id, v.ds): v \in tx_map[tx.id] }
            /\ tx.by \in participants
            /\ tx.via \in vias
        AllSigsPresent(tx) == tx.ss \in { v.ss: v \in tx_map[tx.id] }
        SigConsistent(sig) ==
            /\ sig.id \in all_transactions
            /\ sig.s \in all_sigs
            /\ sig.ds \subseteq participants \union DOMAIN dependency_map
     IN /\ \A tx \in UNION Range(blocks):
             \/ /\ TxConsistent(tx, {"mempool", "miner", "fee-bump"})
                /\ AllSigsPresent(tx)
             \/ Print(<<"~TypeOK blocks", tx>>, FALSE)
        /\ \A tx \in UNION Range(per_block_enabled):
             \/ /\ TxConsistent(tx, {"enabled"})
                /\ AllSigsPresent(tx)
             \/ Print(<<"~TypeOK blocks", tx>>, FALSE)
        /\ \A tx \in next_block:
             \/ /\ TxConsistent(tx, {"mempool", "miner", "fee-bump"})
                /\ AllSigsPresent(tx)
             \/ Print(<<"~TypeOK next_block", tx>>, FALSE)
        /\ \A tx \in mempool:
             \/ /\ TxConsistent(tx, {"mempool"})
                /\ AllSigsPresent(tx)
             \/ Print(<<"~TypeOK mempool", tx>>, FALSE)
        /\ \A tx \in shared_knowledge:
             \/ TxConsistent(tx, {"mempool", "miner", "fee-bump", "direct"})
             \/ Print(<<"~TypeOK shared_knowledge", tx>>, FALSE)
        /\ \A p \in DOMAIN signers_map:
              \/ /\ p \in participants
                 /\ \A sig \in signers_map[p]: sig \in all_sigs
              \/ Print(<<"~TypeOK signers_map", p>>, FALSE)

ConsistentPhase ==
    LET phases == <<InPhase_0, InPhase_1, InPhase_2, InPhase_3>>
     IN Cardinality({ i \in DOMAIN phases: phases[i] }) = 1

NoConcurrentSecretKnowledge ==
    /\ ALICE_IRRATIONAL
       => Print("Not applicable when Alice is not rational", FALSE)
    /\ LET SecretsShared ==
               (all_secrets \intersect UNION { tx.ss: tx \in shared_knowledge })
               \union ({ secretBob } \intersect signers_map[Alice])
               \union ({ secretAlice } \intersect signers_map[Bob])
        IN Cardinality(SecretsShared) <= 1

NoUnexpectedTransactions ==
    ~ALICE_IRRATIONAL => tx_spend_refund_1_bob \notin SentTransactions

NoConflictingTransactions ==
    LET ConflictCheck(txs)==
            LET ids == { tx.id: tx \in txs }
             IN /\ Cardinality(ids) = Cardinality(txs)
                /\ \A id \in ids: ConflictingSet(id) \intersect ids = { id }
     IN /\ ConflictCheck(UNION Range(blocks) \union next_block)
        /\ ConflictCheck(UNION Range(blocks) \union mempool)

NoSingleParticipantTakesAll ==
    /\ ALICE_IRRATIONAL
       => Print("Not applicable when Alice is not rational", FALSE)
    /\ \A p \in participants:
          LET txs_to_p == { tx \in UNION Range(blocks): tx.to = p }
           IN Cardinality({ tx.id: tx \in txs_to_p }) <= 1

TransactionTimelocksEnforced ==
    /\ \A tx \in mempool: Len(blocks) >= TimelockExpirationHeight(tx.id, tx.ds)
    /\ STEALTHY_SEND_POSSIBLE
       => \A tx \in next_block: Len(blocks) >= TimelockExpirationHeight(tx.id, tx.ds)

ExpectedStateOnTimeout ==
    SwapTimedOut => RemainingTransactions \subseteq { tx_lock_B, tx_spend_B }

ExpectedStateOnFinish ==
    ContractFinished =>
        IF SwapTimedOut
        THEN LET ids_left == IF ENABLED ContractAction THEN { tx_lock_B } ELSE {}
              IN /\ RemainingTransactions = { tx_spend_B } \union ids_left
                 /\ MempoolTransactions \subseteq ids_left
                 /\ NextBlockTransactions \subseteq ids_left
        ELSE /\ ~ENABLED ContractAction
             /\ RemainingTransactions = {}
             /\ mempool = {}
             /\ next_block = {}

NoTransactionsRemaining_iff_NotTimedOut ==
    {} = RemainingTransactions <=> ContractFinished /\ ~SwapTimedOut

\* Can use this invariant to check if certain state can be reached.
\* If the CounterExample invariant is violated, then the state has been reached.
CounterExample == TRUE \* /\ ...

(***********************)
(* Temporal properties *)
(***********************)

ContractEventuallyFinished == <>ContractFinished

RevokeLeadsToNonSuccess ==
    /\ ALICE_IRRATIONAL
       => Print("Not applicable when Alice is not rational", FALSE)
    /\ tx_revoke \in NextBlockTransactions ~> ContractFinished /\ ~SwapSuccessful

\*`^\newpage^'
(***************)
(* Init & Next *)
(***************)

Init ==
    /\ blocks = <<>>
    /\ per_block_enabled = <<>>
    /\ next_block = {}
    /\ mempool = {}
    /\ shared_knowledge = {}
    /\ signers_map = [Alice |-> { sigAlice, secretAlice },
                      Bob   |-> { sigBob, secretBob }]

Next == \/ /\ ContractAction
           /\ UpdateEnabledPerBlock
        \/ ContractFinished /\ UNCHANGED fullState

Spec == Init /\ [][Next]_fullState /\ WF_fullState(Next)

================================================================================
