------------------------------ MODULE Logging -------------------------------
EXTENDS SASwap, TLC

\* Add your statements for debug logging here
\* uncomment `ACTION_CONSTRAINT Logging` in config file to enable
Logging ==
    \/ /\ tx_start_B \in ConfirmedTransactions
       /\ PrintT(<<"AAS", AvailableSigs(tx_spend_B, Alice),
                   tx_success \in SentTransactions,
                   secretBob \in {x[2]: x \in shared_knowledge}>>)
    \/ TRUE

=============================================================================
