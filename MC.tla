---- MODULE MC ----
EXTENDS SASwap, TLC, Logging

const_BLOCKS_PER_DAY == 1 \* for the least number of states
const_MAX_DAYS_TO_CONCLUDE == 5
const_STEALTHY_SEND_POSSIBLE == FALSE


=============================================================================
