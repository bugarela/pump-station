----------------------------- MODULE WaterPump -----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANT PUMPS, ALTERNATION_PUMPS, THRESHOLDS

VARIABLES states, requestedStates, requestedPumps, onp, ofp, newLevel, oldLevel, timesActivated

defcon6 == /\newLevel < THRESHOLDS["x1"]

defcon5 == /\ \/ /\oldLevel >= THRESHOLDS["x2"]
                 /\THRESHOLDS["x2"] > newLevel
              \/ /\oldLevel < THRESHOLDS["x1"]
                 /\ THRESHOLDS["x1"] <=newLevel

defcon4 == /\ \/ /\oldLevel < THRESHOLDS["x5"]
                 /\THRESHOLDS["x5"] <= newLevel
                 /\requestedPumps > 4
              \/ /\oldLevel >= THRESHOLDS["x3"]
                 /\THRESHOLDS["x3"] > newLevel

defconPlus1 == /\ \/ /\oldLevel >= THRESHOLDS["x7"]
                     /\THRESHOLDS["x7"] > newLevel
                     /\requestedPumps < 1
                  \/ /\oldLevel >= THRESHOLDS["x6"]
                     /\THRESHOLDS["x6"]> newLevel
                     /\requestedPumps < 2
                  \/ /\oldLevel >= THRESHOLDS["x4"]
                     /\THRESHOLDS["x4"] > newLevel
                     /\requestedPumps < 3

defconMinus1 == /\ \/ /\oldLevel < THRESHOLDS["x11"]
                      /\THRESHOLDS["x11"] <= newLevel
                   \/ /\oldLevel < THRESHOLDS["x10"]
                      /\THRESHOLDS["x10"] <= newLevel
                      /\requestedPumps > 1
                   \/ /\ oldLevel < THRESHOLDS["x9"]
                      /\THRESHOLDS["x9"] <= newLevel
                      /\requestedPumps > 2
                   \/ /\oldLevel < THRESHOLDS["x8"]
                      /\THRESHOLDS["x8"] <= newLevel
                      /\requestedPumps > 3

defcon0 == /\ newLevel > THRESHOLDS["xn"]

defcon == [x \in 0..6 |->
  CASE defcon6 -> 6
     []defcon5 -> 5
     []defcon0 -> 0
     []defconPlus1 -> requestedPumps + 1
     []defconMinus1 -> requestedPumps - 1
     []OTHER -> requestedPumps
]

updateActivationCounter(p) == /\IF \A p2 \in ALTERNATION_PUMPS : p = p2 \/ timesActivated[p2] = 1
                                THEN timesActivated' = [p2 \in ALTERNATION_PUMPS |-> 0]
                                ELSE timesActivated' = [timesActivated EXCEPT ![p] = timesActivated[p] + 1]

activate(p) == /\states[p] = "OFF"
               /\requestedStates' = [requestedStates EXCEPT ![p] = "ON"]
               /\ UNCHANGED <<ofp>>
               /\IF p \in ALTERNATION_PUMPS
                 THEN /\onp = p
                      /\onp' = (p + 1) % 3
                      /\updateActivationCounter(p)
                 ELSE
                      /\IF p = 3
                        THEN /\ \A i \in ALTERNATION_PUMPS : requestedStates[i] \notin {"OFF"}
                             /\ \A i \in ALTERNATION_PUMPS : states[i] \notin {"OFF"}
                        ELSE /\ \A i \in 0..3 : requestedStates[i] \notin {"OFF"}
                             /\ \A i \in 0..3 : states[i] \notin {"OFF"}
                      /\UNCHANGED <<onp, timesActivated>>


deactivate(p) == /\states[p] = "ON"
                 /\requestedStates' = [requestedStates EXCEPT ![p] = "OFF"]
                 /\UNCHANGED <<onp, timesActivated>>
                 /\IF p \in ALTERNATION_PUMPS
                   THEN /\ \A i \in 3..4 : requestedStates[i] \notin {"ON"}
                        /\ \A i \in 3..4 : states[i] \notin {"ON"}
                        /\ofp = p
                        /\ofp' = (p + 1) % 3
                   ELSE UNCHANGED <<ofp>>

selectPumps(pumpCount) ==
  /\requestedPumps' = pumpCount
  /\ \A p \in PUMPS : states[p] \notin {"STARTING", "STOPPING"}
  /\ IF Cardinality({p \in PUMPS : states[p] = "ON"}) < pumpCount
     THEN \E p \in PUMPS : activate(p)
     ELSE IF Cardinality({p \in PUMPS : states[p] = "ON"}) > pumpCount
          THEN \E p \in PUMPS : deactivate(p)
          ELSE UNCHANGED <<states, requestedStates, ofp, onp, timesActivated>>

successON(p) == /\states[p] = "STARTING"
                /\states' = [states EXCEPT ![p] = "ON"]
                /\ UNCHANGED <<requestedStates>>

failureON(p) == /\states[p] = "STARTING"
                /\states' = [states EXCEPT ![p] = "DAMAGED"]
                /\requestedStates' = [requestedStates EXCEPT ![p] = "OFF"]

successOFF(p) == /\states[p] = "STOPPING"
                 /\states' = [states EXCEPT ![p] = "OFF"]
                 /\ UNCHANGED <<requestedStates>>

failureOFF(p) == /\states[p] = "STOPPING"
                 /\states' = [states EXCEPT ![p] = "DAMAGED"]
                 /\requestedStates' = [requestedStates EXCEPT ![p] = "ON"]

switchON(p) == /\states[p] = "OFF"
               /\requestedStates[p] = "ON"
               /\states' = [states EXCEPT ![p] = "STARTING"]

switchOFF(p) == /\states[p] = "ON"
                /\requestedStates[p] = "OFF"
                /\states' = [states EXCEPT ![p] = "STOPPING"]

switchPumps == \E p \in PUMPS : switchON(p) \/ switchOFF(p)

WPInit == /\states = [p \in PUMPS |-> "OFF"]
          /\requestedStates = [p \in PUMPS |-> "OFF"]
          /\onp = 0
          /\ofp = 0
          /\requestedPumps = 0
          /\ newLevel = 120
          /\ oldLevel = 120
          /\timesActivated = [p \in ALTERNATION_PUMPS |-> 0]

waterLevelUp == /\newLevel' = newLevel + 10

waterLevelDown == /\newLevel' = newLevel - 10

pumpSelection == /\selectPumps(defcon[requestedPumps])
                 /\ UNCHANGED <<newLevel, states>>

pumpSwitching == /\switchPumps
                 /\ UNCHANGED <<newLevel, requestedPumps, onp, ofp, requestedStates, timesActivated>>

pumpStatusChange == /\ \E p \in PUMPS : \/ successON(p)
                                        \/ successOFF(p)
                                        \/ failureON(p)
                                        \/ failureOFF(p)
                   /\ UNCHANGED <<newLevel, requestedPumps, onp, ofp, timesActivated>>

waterLevelChange == /\waterLevelUp \/ waterLevelDown
                    /\UNCHANGED <<states, requestedStates, requestedPumps, onp, ofp, timesActivated>>

algorithmStep == IF Cardinality({p \in PUMPS : states[p] = "ON"}) # requestedPumps
                 THEN pumpSwitching
                 ELSE pumpSelection

WPNext == /\ oldLevel' = newLevel
          /\ \/ algorithmStep
             \/ pumpStatusChange
             \/ waterLevelChange

Spec == WPInit /\[][WPNext]_<< states, requestedStates, requestedPumps, onp, ofp, newLevel, oldLevel, timesActivated >>
=============================================================================
\* Modification History
\* Last modified Mon Jul 20 19:15:01 BRT 2020 by gabriela
\* Created Wed Jun 10 07:11:49 BRT 2020 by gabriela
