---------------------------- MODULE HyperProperties ----------------------------
EXTENDS SASwap, TLC

slot_confpairs     == 0
slot_min_dls       == 1
slot_max_soft_dls  == 2
slot_lock_B_last  == 3

ASSUME TLCSet(slot_confpairs, {})
ASSUME TLCSet(slot_min_dls, [ id \in all_transactions |-> UnreachableHeight ])
ASSUME TLCSet(slot_max_soft_dls, [ id \in all_transactions |-> 0 ])
ASSUME TLCSet(slot_lock_B_last, 0)

\* The following actions can be used as 'CONSTRAINTS', but they will not
\* restrict the state space or actions, they can just collect and/or print
\* some useful data.

ShowConfirmed ==
    \/ LET diff == ConfirmedTransactions \ TLCGet(slot_confpairs)
        IN {} /= diff => /\ TLCSet(slot_confpairs,
                                   TLCGet(slot_confpairs) \union ConfirmedTransactions)
                         /\ PrintT(diff)
    \/ TRUE

ShowMinDeadlinesOp(DeadlineOp(_), ReduceOp(_), tlc_slot) ==
    LET cur_dls == [ id \in all_transactions |-> DeadlineOp(id) ]
        old_dls == TLCGet(tlc_slot)
     IN cur_dls /= old_dls
        => LET new_dls == [ id \in all_transactions
                            |-> ReduceOp({old_dls[id], cur_dls[id]}) ]
               f2s(f) == { <<d1, f[d1]>>: d1 \in DOMAIN f }
               diff == f2s(new_dls) \ f2s(old_dls)
            IN /\ TLCSet(tlc_slot, new_dls)
               /\ diff /= {} => PrintT(diff)

ShowMinDeadlines ==
    \/ ShowMinDeadlinesOp(Deadline, Min, slot_min_dls)
    \/ TRUE

ShowMaxSoftDeadlines ==
    \/ ShowMinDeadlinesOp(SoftDeadline, Max, slot_max_soft_dls)
    \/ TRUE

ShowLastBlockToLockB ==
    \/ SwapSuccessful
       => LET lbb == ConfirmationHeight(tx_lock_B)
              prev_lbb == TLCGet(slot_lock_B_last)
           IN lbb > prev_lbb => TLCSet(slot_lock_B_last, lbb) /\ PrintT(<<"LBB", lbb>>)
    \/ TRUE

=============================================================================
