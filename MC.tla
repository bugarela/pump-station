---- MODULE MC ----
EXTENDS WaterPump, TLC

const_pumps ==
{0,1,2,3,4}
----

const_thresholds ==
[ x0 |->  1, x1 |->  10, x2 |->  20, x3 |->  30, x4 |->  40, x5 |->  50, x6 |->  60, x7 |->  70, x8 |->  80, x9 |->  90, x10 |->  100, x11 |->  110, xn |-> 120 ]

level_constraint ==
newLevel \in -10..120
----
simple_check == requestedPumps # 5

allReady == \A p \in PUMPS : states[p] \notin {"STARTING", "STOPPING", "DAMAGED"}
invariant ==
Cardinality({p \in PUMPS : states[p] = "ON"}) > 3 \/ states[4] /= "ON" \/ ~allReady
----
=============================================================================
