----------------------------- MODULE WaterPump -----------------------------
EXTENDS Integers, FiniteSets

CONSTANT PUMPS, THRESHOLDS

VARIABLES states, requestedStates, requestedPumps, onp, ofp, newLevel, oldLevel

defcon6 == /\requestedPumps' = 6
           /\newLevel < THRESHOLDS["x1"]

defcon5 == /\requestedPumps' = 5
           /\ \/ /\oldLevel >= THRESHOLDS["x2"]
                 /\THRESHOLDS["x2"] > newLevel
              \/ /\oldLevel < THRESHOLDS["x1"]
                 /\ THRESHOLDS["x1"] <=newLevel

defcon4 == /\requestedPumps' = 4
           /\ \/ /\oldLevel < THRESHOLDS["x5"]
                 /\THRESHOLDS["x5"] <= newLevel
                 /\requestedPumps > 4
              \/ /\oldLevel >= THRESHOLDS["x3"]
                 /\THRESHOLDS["x3"] > newLevel

defconPlus1 == /\requestedPumps' = requestedPumps + 1
               /\ \/ /\oldLevel >= THRESHOLDS["x7"]
                     /\THRESHOLDS["x7"] > newLevel
                     /\requestedPumps < 1
                  \/ /\oldLevel >= THRESHOLDS["x6"]
                     /\THRESHOLDS["x6"]> newLevel
                     /\requestedPumps < 2
                  \/ /\oldLevel >= THRESHOLDS["x4"]
                     /\THRESHOLDS["x4"] > newLevel
                     /\requestedPumps < 3

defconMinus1 == /\requestedPumps' = requestedPumps - 1
                /\ \/ /\oldLevel < THRESHOLDS["x11"]
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

defcon0 == /\ requestedPumps' = 0
           /\ newLevel > THRESHOLDS["xn"]

defcon == \/ defcon6
          \/ defcon5
          \/ defcon4
          \/ defconPlus1
          \/ defconMinus1

activate(p) == /\states[p] = "OFF"
               /\requestedStates' = [requestedStates EXCEPT ![p] = "ON"]
               /\ UNCHANGED <<ofp>>
               /\IF (p >= 0 /\ p < 3)
                 THEN /\onp = p
                      /\onp' = (p + 1) % 3
                 ELSE /\ \A i \in 0..2 : states[i] \notin {"OFF"}
                      /\onp' = onp

deactivate(p) == /\states[p] = "ON"
                 /\requestedStates' = [requestedStates EXCEPT ![p] = "OFF"]
                 /\ UNCHANGED <<onp>>
                 /\IF (p >= 0 /\ p < 3)
                   THEN /\ \A i \in 3..4 : states[i] \notin {"ON"}
                        /\ofp = p
                        /\ofp' = (p + 1) % 3
                   ELSE ofp' = ofp

selectPumps ==
  /\ \A p \in PUMPS : states[p] \notin {"STARTING", "STOPPING"}
  /\ Cardinality({p \in PUMPS : requestedStates[p] = "ON"}) # requestedPumps
  /\ IF Cardinality({p \in PUMPS : states[p] = "ON"}) < requestedPumps
     THEN \E p \in PUMPS : activate(p)
     ELSE \E p \in PUMPS : deactivate(p)

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

waterLevelUp == /\newLevel' = newLevel + 10
                /\UNCHANGED <<states, requestedStates, requestedPumps, onp, ofp>>

waterLevelDown == /\newLevel' = newLevel - 10
                  /\UNCHANGED <<states, requestedStates, requestedPumps, onp, ofp>>

defconCalculation == /\defcon
                     /\UNCHANGED <<newLevel, states, requestedStates, onp, ofp>>

pumpSelection == /\selectPumps
                 /\ UNCHANGED <<newLevel, states, requestedPumps>>

pumpSwitching == /\switchPumps
                 /\ UNCHANGED <<newLevel, requestedPumps, onp, ofp, requestedStates>>

pumpStatusCheck == /\ \E p \in PUMPS : \/ successON(p)
                                       \/ successOFF(p)
                                       \/ failureON(p)
                                       \/ failureOFF(p)
                   /\ UNCHANGED <<newLevel, requestedPumps, onp, ofp>> 

WPNext == /\ oldLevel' = newLevel
          /\ \/ defconCalculation
             \/ pumpSelection
             \/ pumpSwitching
             \/ pumpStatusCheck
             \/ waterLevelUp
             \/ waterLevelDown
=============================================================================
\* Modification History
\* Last modified Mon Jul 20 19:15:01 BRT 2020 by gabriela
\* Created Wed Jun 10 07:11:49 BRT 2020 by gabriela
