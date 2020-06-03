--------------------------- MODULE SASwap_ZmnSCPxj -----------------------------
\* `.SASwap TLA+ specification (c) by Dmitry Petukhov (https://github.com/dgpv)
\* `.Licensed under a Creative Commons Attribution-ShareAlike 4.0 International
\* `.License <http://creativecommons.org/licenses/by-sa/4.0/>

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT PARTICIPANTS_IRRATIONAL \* Can participants act irrational ?
ASSUME PARTICIPANTS_IRRATIONAL \in BOOLEAN

CONSTANT BLOCKS_PER_DAY
\* More blocks per day means larger state space to check
ASSUME BLOCKS_PER_DAY >= 1

\* A transaction that has no deadline can be 'stalling',
\* i.e. not being sent while being enabled, for this number of days
CONSTANT MAX_DAYS_STALLING
\* More days allowed stalling means larger state space to check
ASSUME MAX_DAYS_STALLING >= 1

\* Is it possible for participants to send transactions
\* bypassing the mempool (give directly to the miner)
CONSTANT STEALTHY_SEND_POSSIBLE
\* When TRUE, the state space is increased dramatically.
ASSUME STEALTHY_SEND_POSSIBLE \in BOOLEAN

\* Operator to create transaction instances
Tx(id, ss, by, to, via) ==
    [ id |-> id, ss |-> ss, to |-> to, by |-> by, via |-> via ]

VARIABLE blocks            \* <<{Tx, ...}, ...>>
VARIABLE next_block        \* {Tx, ...}
VARIABLE mempool           \* {Tx, ...}
VARIABLE shared_knowledge  \* {Tx, ...}
VARIABLE signers_map       \* [participant |-> {allowed_sig, ...}]
VARIABLE per_block_enabled \* <<{Tx, ...}, ...>>
VARIABLE wont_send         \* {id, ...}

fullState  == <<blocks, next_block, signers_map, shared_knowledge, mempool,
                per_block_enabled, wont_send>>
unchangedByMM  == <<blocks, signers_map, shared_knowledge, mempool, wont_send>>

\* A few generic operators
Range(f) == { f[x] : x \in DOMAIN f }
Min(set) == CHOOSE x \in set: \A y \in set : x <= y
Max(set) == CHOOSE x \in set: \A y \in set : x >= y

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

tx_lock_A         == "tx_lock_A"
tx_lock_B         == "tx_lock_B"
tx_success        == "tx_success"
tx_refund_1       == "tx_refund_1"
tx_timeout        == "tx_timeout"
tx_spend_A        == "tx_spend_A"
tx_spend_B        == "tx_spend_B"
tx_spend_success  == "tx_spend_success"
tx_spend_refund_1 == "tx_spend_refund_1"
tx_spend_timeout  == "tx_spend_timeout"

nLockTime == "nLockTime"
nSequence == "nSequence"
NoTimelock == [ days |-> 0, type |-> nLockTime ]

\* If blocks per day are low, the absolute locks need to be shifted,
\* otherwise not all contract paths will be reachable
ABS_LK_OFFSET == CASE BLOCKS_PER_DAY = 1 -> 2
                   [] BLOCKS_PER_DAY = 2 -> 1
                   [] OTHER              -> 0

\* The map of the transactions, their possible destinations and timelocks.
\* Adaptor signatures are modelled by an additional value in the required
\* signature set -- `ss'. For modelling purposes, the secret acts as just another signature.
\* `ds' stands for "destinations", and  `lk' stands for "lock" (timelocks).
\* Only blockheight-based timelocks are modelled.
tx_map == [

    \* 'Contract' transactions -- destinations are other transactions

    tx_lock_A   |-> [ds |-> { tx_success, tx_refund_1, tx_timeout, tx_spend_A },
                     ss |-> { sigAlice }],

    tx_lock_B   |-> [ds |-> { tx_spend_B },
                     ss |-> { sigBob }],

    tx_success  |-> [ds |-> { tx_spend_success },
                     ss |-> { sigAlice, sigBob, secretBob }],

    tx_refund_1 |-> [ds |-> { tx_spend_refund_1 },
                     ss |-> { sigAlice, sigBob, secretAlice },
                     lk |-> [ days |-> ABS_LK_OFFSET + 1, type |-> nLockTime ]],

    tx_timeout  |-> [ds |-> { tx_spend_timeout },
                     ss |-> { sigAlice, sigBob, secretBob},
                     lk |-> [ days |-> ABS_LK_OFFSET + 2, type |-> nLockTime ]],

    \* 'Terminal' transactions -- destinations are participants

    tx_spend_A        |-> [ds |-> { Alice, Bob },
                           ss |-> { sigAlice, sigBob }],

    tx_spend_B        |-> [ds |-> { Alice, Bob },
                           ss |-> { secretAlice, secretBob }],

    tx_spend_success  |-> [ds |-> { Bob },
                           ss |-> { sigBob }],

    tx_spend_refund_1 |-> [ds |-> { Alice },
                           ss |-> { sigAlice } ],

    tx_spend_timeout  |-> [ds |-> { Bob },
                           ss |-> { sigBob }]
]

all_transactions == DOMAIN tx_map

\* `first_transaction' defined so that miner's actions do not need to refer to any
\* contract-specific info, and can just refer to `first_transaction' instead.
first_transaction == tx_lock_A

ConfirmedTransactions == { tx.id: tx \in UNION Range(blocks) }

NextBlockTransactions == { tx.id: tx \in next_block }

NextBlockConfirmedTransactions ==
    ConfirmedTransactions \union NextBlockTransactions

MempoolTransactions == { tx.id: tx \in mempool }

SentTransactions == ConfirmedTransactions \union MempoolTransactions

EnabledTransactions == {tx.id: tx \in UNION Range(per_block_enabled)}

SharedTransactions == {tx.id: tx \in shared_knowledge}

ContractTransactions ==
    { id \in all_transactions:
         \A d \in tx_map[id].ds: d \in all_transactions }

TerminalTransactions ==
    { id \in all_transactions:
         \A d \in tx_map[id].ds: d \in participants }

ASSUME \A id \in all_transactions: \/ id \in TerminalTransactions
                                   \/ id \in ContractTransactions

\* In this contract each transaction has only one parent,
\* so we can use simple mapping from dep_id to parent id
dependency_map ==
    [ dep_id \in UNION { tx_map[id].ds: id \in ContractTransactions }
      |-> CHOOSE id \in ContractTransactions: dep_id \in tx_map[id].ds ]

\* Special destination for the case when funds will still be locked
\* at the contract after the transaction is spent
Contract == "Contract"

DstSet(id) ==
    IF id \in ContractTransactions THEN { Contract } ELSE tx_map[id].ds

\* The CASE statement has no 'OTHER' clause - only single dst is expected
SingleDst(id) == CASE id \in ContractTransactions -> Contract
                   [] Cardinality(tx_map[id].ds) = 1
                      -> CHOOSE d \in tx_map[id].ds: TRUE

\* The set of transactions conflicting with the given transaction
ConflictingSet(id) ==
    IF id \in DOMAIN dependency_map
    THEN { dep_id \in DOMAIN dependency_map:
           dependency_map[dep_id] = dependency_map[id] }
    ELSE { id }

\* Transaction also conflicts with itself
ASSUME \A id \in all_transactions: id \in ConflictingSet(id)

ConfirmationHeight(id) ==
    CHOOSE bn \in DOMAIN blocks: \E tx \in blocks[bn]: tx.id = id

\* All the transactions the given transaction depends on.
\* Because each transaction can only have one dependency in our model,
\* all dependencies form a chain, not a tree.
RECURSIVE DependencyChain(_)
DependencyChain(id) ==
    IF id \in DOMAIN dependency_map
    THEN { id } \union DependencyChain(dependency_map[id])
    ELSE { id }

\* All the transactions that depend on the given transaction.
\* Dependants form a tree, but the caller is interested in just a set.
RECURSIVE AllDependants(_)
AllDependants(id) ==
    LET dependants == tx_map[id].ds \ participants
     IN IF dependants = {}
        THEN { id }
        ELSE dependants \union UNION { AllDependants(d_id): d_id \in dependants }

\* All transactions that cannot ever become valid because other, conflicting
\* transactions were confirmed befor them
InvalidatedTransactions ==
    UNION { { c_id } \union AllDependants(c_id): c_id \in
            UNION { ConflictingSet(id) \ { id }: id \in ConfirmedTransactions } }

\* All transactions that is not yet sent/confirmed, and have a chance to be.
RemainingTransactions ==
    ((all_transactions \ ConfirmedTransactions) \ InvalidatedTransactions)

Timelock(id) == IF "lk" \in DOMAIN tx_map[id] THEN tx_map[id].lk ELSE NoTimelock

UnreachableHeight == 2^30+(2^30-1)

\* Calculate the height at which the timelock for the given transaction
\* expires, taking BLOCKS_PER_DAY and dependencies confirmation into account
TimelockExpirationHeight(id) ==
    LET lk == Timelock(id)
     IN CASE lk.type = nLockTime
             -> lk.days * BLOCKS_PER_DAY
          [] lk.type = nSequence
              -> IF dependency_map[id] \in ConfirmedTransactions
                 THEN ConfirmationHeight(dependency_map[id])
                      + lk.days * BLOCKS_PER_DAY
                 ELSE UnreachableHeight

\* "Hard" deadline for transaction means that it is unsafe to publish
\* the transaction after the deadline
Deadline(id) ==
    LET hs == { TimelockExpirationHeight(c_id):
                c_id \in (ConflictingSet(id) \ { id }) \ wont_send }
        higher_hs == { h \in hs: h > TimelockExpirationHeight(id) }
     IN IF higher_hs = {}
        THEN UnreachableHeight
        ELSE Min(higher_hs)

\* "Soft" deadline for transaction means that after the deadline,
\* mining the transaction will mean that it was 'stalling' for too long
SoftDeadline(id) ==
    LET dl == Deadline(id)
        h == TimelockExpirationHeight(id)
     IN IF dl = UnreachableHeight
        THEN IF id \in EnabledTransactions
             THEN ( CHOOSE en \in DOMAIN per_block_enabled:
                        \E tx \in per_block_enabled[en]: tx.id = id )
                  + MAX_DAYS_STALLING * BLOCKS_PER_DAY
             ELSE IF h /= UnreachableHeight
                  THEN h + MAX_DAYS_STALLING * BLOCKS_PER_DAY
                  ELSE 0
        ELSE dl

SigsAvailable(id, sender, to) ==
    LET secrets_shared ==
            UNION { tx.ss \intersect all_secrets: tx \in shared_knowledge }
        sigs_shared ==
            UNION { tx.ss: tx \in { tx \in shared_knowledge: /\ tx.id = id
                                                             /\ tx.to = to } }
     IN sigs_shared \union secrets_shared \union signers_map[sender]

DependencySatisfied(id, ids) ==
    id \in DOMAIN dependency_map => dependency_map[id] \in ids

IsSpendableTx(tx, other_ids) ==
    /\ {} = ConflictingSet(tx.id) \intersect other_ids
    /\ DependencySatisfied(tx.id, other_ids)
    /\ tx.ss \subseteq SigsAvailable(tx.id, tx.by, tx.to)
    /\ Len(blocks) >= TimelockExpirationHeight(tx.id)

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
    LET Ss(id) == (tx_map[id].ss \intersect signers_map[by]) \ all_secrets
        txs == { Tx(id, Ss(id), by, SingleDst(id), "direct"): id \in ids }
     IN /\ ShareKnowledge(txs)
        /\ shared_knowledge' /= shared_knowledge \* not a new knowledge => fail

\* Txs enabled at the current cycle, used to update per_block_enabled vector
NewlyEnabledTxs ==
    { tx \in
      UNION
      { UNION
        {
          {
            Tx(id, tx_map[id].ss, sender, to, "enabled"): to \in DstSet(id)
          }: id \in RemainingTransactions
        }: sender \in participants
      }: /\ ~\E etx \in UNION Range(per_block_enabled): etx.id = tx.id
         /\ IsSpendableTx(tx, ConfirmedTransactions)
    }

SendTransactionToMempool(id, sender, to) ==
    LET tx == Tx(id, tx_map[id].ss, sender, to, "mempool")
     IN /\ IsSpendableTx(tx, SentTransactions)
        /\ Len(blocks) < Deadline(id)
        /\ mempool' = mempool \union { tx }
        /\ ShareKnowledge({ tx })

\* Give tx directly to miner, bypassing global mempool
\* No Deadline check because information is not shared,
\* and after the block is mined, there's no possible contention
\* unless the block is orphaned. Orphan blocks are not modelled,
\* and therefore there's no need for additional restriction
\* as any state space restriction can possibly mask some other issue
SendTransactionToMiner(id, sender, to) ==
    /\ STEALTHY_SEND_POSSIBLE
    /\ LET tx == Tx(id, tx_map[id].ss, sender, to, "miner")
       IN /\ IsSpendableTx(tx, NextBlockConfirmedTransactions)
          /\ next_block' = next_block \union { tx }

SendTransaction(id, sender, to) ==
    \/ /\ SendTransactionToMempool(id, sender, to)
       /\ UNCHANGED next_block
    \/ /\ SendTransactionToMiner(id, sender, to)
       /\ UNCHANGED <<mempool, shared_knowledge>>

SendSomeTransaction(ids, sender) ==
    LET SendSome(filtered_ids) ==
            \E id \in filtered_ids \ wont_send:
            \E to \in (IF id \in ContractTransactions
                       THEN {Contract}
                       ELSE tx_map[id].ds \intersect { sender }):
                SendTransaction(id, sender, to)
        terminal_ids == ids \intersect TerminalTransactions
     IN CASE PARTICIPANTS_IRRATIONAL
             -> SendSome(ids) \* Irrational participants do no prioritization
          [] ENABLED SendSome(terminal_ids)
             -> SendSome(terminal_ids) \* Can send terminal tx => do it immediately
          [] OTHER
             -> SendSome(ids \ terminal_ids)

HasCustody(ids, participant) ==
    \E id \in ids: \E tx \in UNION Range(blocks): tx.id = id /\ tx.to = participant

\* Sharing secrets or keys has to occur before deadline to send tx_success
TooLateToShare == Len(blocks) >= Deadline(tx_success)

(***********************)
(* Participant actions *)
(***********************)

\* Helper operators to declutter the action expressions
NoSending == UNCHANGED <<mempool, next_block>>
NoKeysShared == UNCHANGED signers_map
NoKnowledgeShared == UNCHANGED shared_knowledge

AliceAction ==
    LET Send(ids) == SendSomeTransaction(ids, Alice)
        Share(ids) == ShareTransactions(ids, Alice)
        SafeToSend(id) ==
            CASE PARTICIPANTS_IRRATIONAL
                 -> TRUE \* Unsafe txs are OK for irrational Alice
              [] secretAlice \in tx_map[id].ss
                 \* Once Alice shared tx_success, should never send out secretAlice
                 -> \/ tx_success \notin {tx.id: tx \in shared_knowledge}
                    \/ id = tx_spend_B \* unless this is a transaction to get B
                                       \* which does not in fact expose secrets
              [] OTHER -> TRUE
     IN \/ /\ Send({ id \in RemainingTransactions: SafeToSend(id) })
           /\ NoKeysShared
        \/ /\ { tx_lock_A, tx_lock_B } \subseteq ConfirmedTransactions
           /\ ~({ tx_success, tx_timeout } \subseteq SharedTransactions)
           /\ tx_refund_1 \notin SentTransactions
           /\ Share({ tx_success, tx_timeout })
           /\ NoSending /\ NoKeysShared
        \/ /\ { tx_lock_A, tx_lock_B } \subseteq ConfirmedTransactions
           /\ { tx_success, tx_refund_1, tx_timeout } \subseteq SharedTransactions
           /\ secretBob \in signers_map[Alice] \* Bob gave Alice his secret
           /\ sigAlice \notin signers_map[Bob] \* Alice did not yet gave Bob her key
           /\ tx_success \notin ConfirmedTransactions \* Swap went on-chain => no key sharing
           /\ ~TooLateToShare
           /\ signers_map' = [signers_map  \* Give Alice's key to Bob
                              EXCEPT ![Bob] = @ \union { sigAlice }]
           /\ NoSending /\ NoKnowledgeShared

BobAction ==
    LET Send(ids) == SendSomeTransaction(ids, Bob)
        Share(ids) == ShareTransactions(ids, Bob)
        tx_success_sigs == SigsAvailable(tx_success, Bob, Contract)
     IN \/ /\ Send(RemainingTransactions)
           /\ NoKeysShared /\ UNCHANGED wont_send
        \/ /\ tx_refund_1 \notin SharedTransactions
           /\ tx_success \notin SentTransactions
           /\ tx_timeout \notin SentTransactions
           /\ Share({ tx_refund_1 })
           /\ wont_send' = wont_send \union {tx_timeout}
           /\ NoSending /\ NoKeysShared
        \/ /\ { tx_lock_A, tx_lock_B } \subseteq ConfirmedTransactions
           /\ { tx_success, tx_refund_1, tx_timeout } \subseteq SharedTransactions
           /\ tx_success \notin SentTransactions
           /\ tx_timeout \notin SentTransactions
           /\ secretAlice \notin tx_success_sigs
           /\ secretBob \notin signers_map[Alice]
           /\ ~TooLateToShare
           /\ signers_map' = [signers_map \* Give secretBob to Alice
                              EXCEPT ![Alice] = @ \union { secretBob }]
           /\ wont_send' = wont_send \ {tx_timeout}
           /\ NoSending /\ NoKnowledgeShared

MempoolMonitorActionRequired ==
    \E tx \in mempool: /\ Len(blocks) + 1 = Deadline(tx.id)
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
    LET tx == CHOOSE tx \in mempool: Len(blocks) + 1 = Deadline(tx.id)
        txs_to_bump == { tx } \union { dptx \in mempool:
                                      /\ tx.id \in DOMAIN dependency_map
                                      /\ dptx.id = dependency_map[tx.id]
                                      /\ dptx.id \notin NextBlockTransactions }
     IN next_block' =
            { nbtx \in next_block: \* conflicting txs are expunged from next_block
              {} = DependencyChain(nbtx.id) \intersect
                     UNION { ConflictingSet(bmptx.id): bmptx \in txs_to_bump } }
            \union { [bmptx EXCEPT !.via = "fee-bump"]: bmptx \in txs_to_bump }

(****************)
(* Miner action *)
(****************)

IncludeTxIntoBlock ==
    /\ \E tx \in mempool:
          /\ {} = ConflictingSet(tx.id) \intersect NextBlockConfirmedTransactions
          /\ DependencySatisfied(tx.id, NextBlockConfirmedTransactions)
          /\ next_block' = next_block \union { tx }
    /\ UNCHANGED <<blocks, mempool, shared_knowledge>>

\* Needed to restrict the state space, so that model checking is feasible
CanMineEmptyBlock ==
    /\ first_transaction \in ConfirmedTransactions
    /\ LET soft_dls == { SoftDeadline(id): id \in RemainingTransactions }
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

AliceLostByMisbehaving ==
    /\ HasCustody({ tx_spend_B }, Bob)
    /\ HasCustody({ tx_spend_success, tx_spend_timeout }, Bob)

BobLostByBeingLateOnSuccess ==
    /\ HasCustody({ tx_spend_B }, Alice)
    /\ HasCustody({ tx_spend_refund_1 }, Alice)

SwapUnnaturalEnding == BobLostByBeingLateOnSuccess \/ AliceLostByMisbehaving

\* The normal, 'natural' cases.

SwapSuccessful ==
    /\ HasCustody({ tx_spend_B }, Alice)
    /\ HasCustody({ tx_spend_A, tx_spend_success, tx_spend_timeout }, Bob)

SwapAborted ==
    /\ HasCustody({ tx_spend_A, tx_spend_refund_1 }, Alice)
    /\ \/ HasCustody({ tx_spend_B }, Bob)
       \/ tx_lock_B \notin SentTransactions

\* Deadlock is possible by design.
\* See https://lists.linuxfoundation.org/pipermail/bitcoin-dev/2020-June/017918.html
SwapDeadlocked ==
    LET stx == Tx(tx_success, tx_map[tx_success].ss, Bob, Contract, "test")
        rtx == Tx(tx_refund_1, tx_map[tx_refund_1].ss, Alice, Contract, "test")
     IN /\ ConfirmedTransactions = {tx_lock_A, tx_lock_B}
        /\ IsSpendableTx(stx, SentTransactions)
        /\ IsSpendableTx(rtx, SentTransactions)
        /\ ~ENABLED AliceAction
        /\ ~ENABLED BobAction

\* All possible endings of the contract
ContractFinished == \/ SwapSuccessful
                    \/ SwapAborted
                    \/ SwapDeadlocked
                    \/ PARTICIPANTS_IRRATIONAL /\ SwapUnnaturalEnding

\* Actions in the contract when it is not yet finished. Separated into
\* dedicated operator to be able to test `ENABLED ContractAction`
ContractAction ==
    \/ AliceAction               /\ UNCHANGED <<blocks, wont_send>>
    \/ BobAction                 /\ UNCHANGED blocks
    \/ IF MempoolMonitorActionRequired
       THEN MempoolMonitorAction /\ UNCHANGED unchangedByMM
       ELSE MinerAction          /\ UNCHANGED <<signers_map, wont_send>>

(***************)
(* Invariants  *)
(***************)

TypeOK ==
    LET TxConsistent(tx, vias) == /\ tx.id \in all_transactions
                                  /\ tx.ss \subseteq tx_map[tx.id].ss
                                  /\ tx.to \in DstSet(tx.id)
                                  /\ tx.by \in participants
                                  /\ tx.via \in vias
        AllSigsPresent(tx) == tx.ss = tx_map[tx.id].ss
        SigConsistent(sig) == /\ sig.id \in all_transactions
                              /\ sig.s \in all_sigs
                              /\ sig.ds \subseteq participants
                                                  \union DOMAIN dependency_map
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
              \/ p \in participants /\ \A sig \in signers_map[p]: sig \in all_sigs
              \/ Print(<<"~TypeOK signers_map", p>>, FALSE)

OnlyWhenParticipantsAreRational ==
    PARTICIPANTS_IRRATIONAL
       => Assert(FALSE, "Not applicable when participants are not rational")

NoConcurrentSecretKnowledge ==
    /\ OnlyWhenParticipantsAreRational
    /\ LET SecretsShared ==
               (all_secrets \intersect UNION { tx.ss: tx \in shared_knowledge })
               \union ({ secretBob } \intersect signers_map[Alice])
               \union ({ secretAlice } \intersect signers_map[Bob])
        IN Cardinality(SecretsShared) <= 1

NoConflictingTransactions ==
    LET ConflictCheck(txs)==
            LET ids == { tx.id: tx \in txs }
             IN /\ Cardinality(ids) = Cardinality(txs)
                /\ \A id \in ids: ConflictingSet(id) \intersect ids = { id }
     IN /\ ConflictCheck(UNION Range(blocks) \union next_block)
        /\ ConflictCheck(UNION Range(blocks) \union mempool)

NoSingleParticipantTakesAll ==
    /\ OnlyWhenParticipantsAreRational
    /\ \A p \in participants:
          LET txs_to_p == { tx \in UNION Range(blocks): tx.to = p }
           IN Cardinality({ tx.id: tx \in txs_to_p }) <= 1

TransactionTimelocksEnforced ==
    /\ \A tx \in mempool: Len(blocks) >= TimelockExpirationHeight(tx.id)
    /\ STEALTHY_SEND_POSSIBLE
       => \A tx \in next_block: Len(blocks) >= TimelockExpirationHeight(tx.id)

ExpectedStateOnAbort ==
    SwapAborted
    => LET ids_left == IF ENABLED ContractAction THEN { tx_lock_B } ELSE {}
        IN RemainingTransactions \subseteq { tx_spend_B } \union ids_left

ExpectedStateOnSuccess ==
    SwapSuccessful => /\ ~ENABLED ContractAction \/ Print(<<ENABLED AliceAction, ENABLED BobAction, RemainingTransactions>>, FALSE)
                      /\ RemainingTransactions = {}
                      /\ mempool = {}
                      /\ next_block = {}

\* Can use this invariant to check if certain state can be reached.
\* If the CounterExample invariant is violated, then the state has been reached.
CounterExample == TRUE \* /\ ...

(***********************)
(* Temporal properties *)
(***********************)

ContractEventuallyFinished == <>ContractFinished

(***************)
(* Init & Next *)
(***************)

Init ==
    /\ blocks = <<>>
    /\ per_block_enabled = <<>>
    /\ next_block = {}
    /\ mempool = {}
    /\ shared_knowledge = {}
    /\ wont_send = {}
    /\ signers_map = [Alice |-> { sigAlice, secretAlice },
                      Bob   |-> { sigBob, secretBob }]

Next == \/ /\ ContractAction
           /\ UpdateEnabledPerBlock
        \/ ContractFinished /\ UNCHANGED fullState

Spec == Init /\ [][Next]_fullState /\ WF_fullState(Next)

================================================================================
