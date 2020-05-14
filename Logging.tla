------------------------------ MODULE Logging -------------------------------
EXTENDS SASwap, TLC

\* Add your statements for debug logging here
\* uncomment `ACTION_CONSTRAINT Logging` in config file to enable
Logging ==
    \* \/ PrintT(<<"ST", fullState>>)
    \* Uncomment to print the deadlines for transactions at the time tx_timeout confirmed
    \* \/ tx_spend_timeout \in ConfirmedTransactions
    \*     => Assert(FALSE,
    \*               UNION {{<<id, Deadline(id, v.ds)>>:
    \*                       v \in {v \in tx_map[id]: Deadline(id, v.ds) /= UnreachableHeight}}:
    \*                      id \in all_transactions})
    \/ TRUE

=============================================================================
