-------------------------------- MODULE SASwap ---------------------------------
\* `.SASwap TLA+ specification (c) by Dmitry Petukhov (https://github.com/dgpv)
\* `.This SASwap TLA+ specification is licensed under a Creative Commons
\* `.Attribution-ShareAlike 4.0 International License
\* `.<http://creativecommons.org/licenses/by-sa/4.0/>

EXTENDS Naturals, Sequences, TLC

CONSTANT BLOCKS_PER_DAY
ASSUME BLOCKS_PER_DAY > 0

CONSTANT MAX_DAYS_TO_CONCLUDE
ASSUME MAX_DAYS_TO_CONCLUDE > 4

CONSTANT STEALTHY_SEND_POSSIBLE
ASSUME STEALTHY_SEND_POSSIBLE \in BOOLEAN

VARIABLES blocks, block_txs, mempool, shared_knowledge, sigs, signers_map

sigState == <<sigs, signers_map>>
networkState == <<blocks, block_txs, mempool>>
fullState == <<networkState, sigState, shared_knowledge>>

\* Can use this predicate to limit possible state space by
\* ignoring the states after MAX_DAYS_TO_CONCLUDE has passed
ConcludedInFiniteDays ==
    Len(blocks) <= BLOCKS_PER_DAY * MAX_DAYS_TO_CONCLUDE

\* Can use this predicate to limit possible state space by
\* ignoring the states where nothing was sent/confirmed in a day
EachDaySomethingIsConfirmed ==
    ~\E bn \in DOMAIN blocks:
        \A bn_next \in bn..bn+BLOCKS_PER_DAY-1:
            /\ bn_next \in DOMAIN blocks
            /\ blocks[bn_next] = {}

\* Define unique values to avoid using strings everywhere

Alice == "Alice"
Bob   == "Bob"

sigAlice    == "sigAlice"
sigBob      == "sigBob"
secretAlice == "secretAlice"
secretBob   == "secretBob"

tx_start_A  == "tx_start_A"
tx_start_B  == "tx_start_B"
tx_success  == "tx_success"
tx_refund_1 == "tx_refund_1"
tx_revoke   == "tx_revoke"
tx_refund_2 == "tx_refund_2"
tx_timeout  == "tx_timeout"

tx_spend_B        == "tx_spend_B"
tx_spend_success  == "tx_spend_success"
tx_spend_refund_1 == "tx_spend_refund_1"
tx_spend_refund_2 == "tx_spend_refund_2"
tx_spend_timeout  == "tx_spend_timeout"

participants == {Alice, Bob}

all_sigs == {sigAlice, sigBob, secretAlice, secretBob}

Counterparty(p) == CHOOSE c \in participants: c /= p

ConfirmedTransactions ==
    UNION {blocks[bn] : bn \in DOMAIN blocks}

SentTransactions == ConfirmedTransactions \union mempool

dependency_map == [tx_success  |-> tx_start_A,
                   tx_refund_1 |-> tx_start_A,
                   tx_revoke   |-> tx_start_A,
                   tx_refund_2 |-> tx_revoke,
                   tx_timeout  |-> tx_revoke,
                   tx_spend_B        |-> tx_start_B,
                   tx_spend_success  |-> tx_success,
                   tx_spend_refund_1 |-> tx_refund_1,
                   tx_spend_refund_2 |-> tx_refund_2,
                   tx_spend_timeout  |-> tx_timeout]

all_transactions ==
    \* each transacton is either dependant or a dependency
    DOMAIN dependency_map \union {dependency_map[x]:
                                  x \in DOMAIN dependency_map}

\* transactions that are mutually exclusive
conflicts == {{tx_success, tx_refund_1, tx_revoke},
              {tx_refund_2, tx_timeout}}

\* transactions Alice initially shares signatures on
phase0_to_share_Alice == {tx_revoke, tx_timeout}

\* transactions Bob initially shares signatures on
phase0_to_share_Bob == {tx_refund_1, tx_revoke, tx_refund_2, tx_timeout}

HasDependencies(tx) == tx \in DOMAIN dependency_map

DependencyConfirmed(tx) == dependency_map[tx] \in ConfirmedTransactions

DependencySent(tx) == DependencyConfirmed(tx) \/ dependency_map[tx] \in mempool

DependencyBlock(tx) ==
    CHOOSE bn \in DOMAIN blocks: dependency_map[tx] \in blocks[bn]

NoConflicts(tx) ==
    \A cfl_set \in conflicts:
        \/ tx \notin cfl_set
        \/ ~\E cfl_tx \in cfl_set \ {tx}: cfl_tx \in SentTransactions

SharedSecrets ==
    {x[2]: x \in {xx \in shared_knowledge:
                    xx[2] \in {secretAlice, secretBob}}}

\* Signatures currently available to the sender
\* includes sigs made by the sender themself,
\* and anything from shared knowledge
AvailableSigs(tx, sender) ==
   sigs[sender][tx]
      \union {x[2]: x \in {xx \in shared_knowledge: xx[1] = tx}}
      \union SharedSecrets

\* All signatures known for certain transaction.
\* These go to shared knowledge when the transaction is mined
\* (unless already shared)
\* This is a simplification, because in general there could be
\* unpublished signatures when threshold signing is used.
\* But for this contract, this is OK.
AllSigsForTx(tx) == UNION {sigs[sender][tx]: sender \in participants}

\* Adaptor signatures are modelled as having to supply 3 values
\* for the signature set, where two values are the sigs,
\* and one value is a secret.
\* For modelling purposes, the secret acts as just another sig.

SpendConditionsSatisfied(tx, sender) ==
    LET HasSigs(ss) == ss \subseteq AvailableSigs(tx, sender)
    IN \/ /\ tx = tx_start_A
          /\ HasSigs({sigAlice})
       \/ /\ tx = tx_start_B
          /\ HasSigs({sigBob})
       \/ /\ tx = tx_success
          /\ HasSigs({sigAlice, sigBob, secretBob})
       \/ /\ tx = tx_refund_1
          /\ HasSigs({sigAlice, sigBob, secretAlice})
          /\ Len(blocks) >= BLOCKS_PER_DAY
       \/ /\ tx = tx_revoke
          /\ HasSigs({sigAlice, sigBob})
          /\ Len(blocks) >= BLOCKS_PER_DAY*2
       \/ /\ tx = tx_refund_2
          /\ HasSigs({sigAlice, sigBob, secretAlice})
          /\ DependencyConfirmed(tx)
          /\ Len(blocks) >= DependencyBlock(tx) + BLOCKS_PER_DAY
       \/ /\ tx = tx_timeout
          /\ HasSigs({sigAlice, sigBob})
          /\ DependencyConfirmed(tx)
          /\ Len(blocks) >= DependencyBlock(tx) + BLOCKS_PER_DAY*2
       \/ /\ tx = tx_spend_B
          /\ HasSigs({secretAlice, secretBob})
       \/ /\ tx = tx_spend_success
          /\ HasSigs({sigBob})
       \/ /\ tx = tx_spend_refund_1
          /\ HasSigs({sigAlice})
          /\ DependencyConfirmed(tx)
          /\ Len(blocks) >= DependencyBlock(tx) + BLOCKS_PER_DAY
       \/ /\ tx = tx_spend_refund_2
          /\ HasSigs({sigAlice})
       \/ /\ tx = tx_spend_timeout
          /\ HasSigs({sigBob})

       \* Unclear what the result of this tx should be
       \* \/ /\ tx = tx_spend_refund_1_cooperative

CanEnterMempool(tx, sender) ==
    /\ tx \notin SentTransactions
    /\ NoConflicts(tx)
    /\ \/ HasDependencies(tx) /\ DependencySent(tx)
       \/ ~HasDependencies(tx)
    /\ SpendConditionsSatisfied(tx, sender)

Share(knowledge) == shared_knowledge' = shared_knowledge \union knowledge

\* Note that the sigs record-of-records may not be the most elegant
\* data structure for the purpose, might be worth it to explore other options
SignTx(tx, ss, signer) ==
    /\ \A s \in ss: s \in signers_map[signer]
    /\ sigs' = [sigs EXCEPT
                  ![signer] = [sigs[signer] EXCEPT
                                 ![tx] = sigs[signer][tx] \union ss]]

SendTx(tx, sender) ==
    /\ CanEnterMempool(tx, sender)
    /\ mempool' = mempool \union {tx}
    /\ Share({<<tx, s>>: s \in sigs[sender][tx]})

\* Give tx directly to miner, bypassing global mempool 
StealthySendTx(tx, sender) ==
    /\ STEALTHY_SEND_POSSIBLE
    /\ CanEnterMempool(tx, sender)
    /\ block_txs' = block_txs \union {tx}

\* If participant has a transaction ready to be sent,
\* they can send it to mempool, or stealthy to the miner
\* (if STEALTHY_SEND_POSSIBLE is TRUE)
SendSomething ==
    \E sender \in participants:
        \E tx \in all_transactions:
            \/ /\ SendTx(tx, sender)
               /\ UNCHANGED block_txs
            \/ /\ StealthySendTx(tx, sender)
               /\ UNCHANGED <<mempool, shared_knowledge>>

(***********************)
(* Participant actions *)
(***********************)

\* Conditions to divide the action into phases according to original spec

Phase_3_cond == tx_start_B \in ConfirmedTransactions
Phase_2_cond == tx_start_A \in ConfirmedTransactions
Phase_1_cond ==
    /\ \A tx \in phase0_to_share_Alice:
           \E signed_pair \in shared_knowledge: signed_pair = <<tx, sigAlice>>
    /\ \A tx \in phase0_to_share_Bob:
           \E signed_pair \in shared_knowledge: signed_pair = <<tx, sigBob>>

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


\* helper operators to declutter the action expressions
NoSigning == UNCHANGED sigState
NothingShared == UNCHANGED shared_knowledge

AliceAction ==
    LET Sign(tx, ss) == SignTx(tx, ss, Alice)
    IN \/ /\ InPhase_0
          /\ Share({<<tx, sigAlice>>: tx \in phase0_to_share_Alice})
          /\ NoSigning
       \/ /\ InPhase_1
          /\ Sign(tx_start_A, {sigAlice})
          /\ NothingShared
       \/ /\ InPhase_2
          /\ \* Do nothing or refund, if timelock allows
             \/ NoSigning
             \/ Sign(tx_refund_1, {sigAlice, secretAlice})
          /\ NothingShared
       \/ /\ InPhase_3
          /\ \/ /\ Share({<<tx_success, sigAlice>>})
                /\ NoSigning
             \/ \* Can revoke on short path until tx_success is shared
                /\ <<tx_success, sigAlice>> \notin shared_knowledge
                /\ Sign(tx_refund_1, {sigAlice, secretAlice})
                /\ NothingShared
             \/ /\ \/ Sign(tx_spend_B, {secretAlice})
                   \/ Sign(tx_refund_2, {sigAlice, secretAlice})
                   \/ Sign(tx_spend_refund_1, {sigAlice, secretAlice})
                   \/ Sign(tx_spend_refund_2, {sigAlice, secretAlice})
                /\ NothingShared

BobAction ==
    LET Sign(tx, ss) == SignTx(tx, ss, Bob)
    IN \/ /\ InPhase_0
          /\ Share({<<tx, sigBob>>: tx \in phase0_to_share_Bob})
          /\ NoSigning
       \/ /\ InPhase_1 \* No specific actions
          /\ NoSigning
          /\ NothingShared
       \/ /\ InPhase_2
          /\ Sign(tx_start_B, {sigBob})
          /\ NothingShared
       \/ /\ InPhase_3
          /\ \/ Sign(tx_spend_B, {secretBob})
             \/ Sign(tx_success, {sigBob, secretBob})
             \/ Sign(tx_spend_success, {sigBob})
             \/ Sign(tx_timeout, {sigBob})
             \/ Sign(tx_spend_timeout, {sigBob})
          /\ NothingShared

IncludeTxIntoBlock ==
    /\ \E tx \in mempool:
          /\ IF HasDependencies(tx)
             THEN \/ DependencyConfirmed(tx)
                  \/ dependency_map[tx] \in block_txs
             ELSE TRUE
          /\ block_txs' = block_txs \union {tx}
    /\ UNCHANGED <<blocks, mempool, shared_knowledge>>

MineTheBlock ==
    /\ blocks' = Append(blocks, block_txs)
    /\ mempool' = mempool \ block_txs
    /\ Share(UNION {{<<tx, s>>: s \in AllSigsForTx(tx)}:
                         tx \in block_txs \ mempool})
    /\ block_txs' = {}

MinerAction == IncludeTxIntoBlock \/ MineTheBlock

\*`^\newpage^'
(***************)
(* Invariants  *)
(***************)

TypeOK ==
    /\ \A pair \in shared_knowledge:
            /\ pair[1] \in all_transactions
            /\ pair[2] \in all_sigs
    /\ DOMAIN sigs = participants
    /\ DOMAIN signers_map = participants
    /\ \A sender \in DOMAIN sigs:
          \A tx \in DOMAIN sigs[sender]:
             /\ tx \in all_transactions
             /\ sigs[sender][tx] \subseteq all_sigs

ConsistentPhase ==
    LET phases == <<InPhase_0, InPhase_1, InPhase_2, InPhase_3>>
    IN /\ \E i \in DOMAIN phases: phases[i]
       /\ \A i \in DOMAIN phases:
             IF phases[i]
             THEN ~\E ii \in DOMAIN phases: ii /= i /\ phases[ii]
             ELSE TRUE

NoConcurrentSecretKnowledge ==
    \/ tx_spend_B \in SentTransactions
    \/ ~({secretAlice, secretBob} \subseteq SharedSecrets)

\* Can use this invariant to check if certain state can be reached
\* If the CounterExample invariant is violated, then the state
\* has been reached.
CounterExample == TRUE \* /\ ...

(*************************************************)
(* Temporal properties, Not tested at the moment *)
(*************************************************)

AllEventuallyConfirmed ==
    \A tx \in all_transactions: <>(tx \in ConfirmedTransactions)

SuccessTxLeadsToSpentB ==
    tx_success \in SentTransactions ~> tx_spend_B \in ConfirmedTransactions

(*******************)
(* High-level spec *)
(*******************)

Init ==
    /\ blocks = <<>>
    /\ block_txs = {}
    /\ mempool = {}
    /\ shared_knowledge = {}
    /\ sigs = [Alice |-> [tx \in all_transactions |-> {}],
               Bob |-> [tx \in all_transactions |-> {}]]
    /\ signers_map = [Alice |-> {sigAlice, secretAlice},
                      Bob   |-> {sigBob, secretBob}]


Next ==
    /\ ConcludedInFiniteDays
    /\ EachDaySomethingIsConfirmed
       \* Note that signers_map is always unchanged at the moment
    /\ \/ AliceAction   /\ UNCHANGED <<networkState, signers_map>>
       \/ BobAction     /\ UNCHANGED <<networkState, signers_map>>
       \/ SendSomething /\ UNCHANGED <<blocks, sigState>>
       \/ MinerAction   /\ UNCHANGED sigState

Spec == Init /\ [][Next]_fullState \* /\ WF_networkState(Next)
             
================================================================================
