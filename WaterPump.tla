----------------------------- MODULE WaterPump -----------------------------
EXTENDS Integers, FiniteSets

CONSTANT PUMPS, THRESHOLDS

VARIABLES states, requestedStates, requestedPumps, onp, ofp, newLevel, oldLevel

defcon == \/ /\ requestedPumps' = 0
             /\ newLevel > THRESHOLDS["xn"]
          \/ /\ requestedPumps' = requestedPumps - 1
             /\ \/ oldLevel < THRESHOLDS["x11"] /\ THRESHOLDS["x11"] <= newLevel
                \/ oldLevel < THRESHOLDS["x10"] /\THRESHOLDS["x10"] <= newLevel /\ requestedPumps > 1
                \/ oldLevel < THRESHOLDS["x9"] /\ THRESHOLDS["x9"] <= newLevel /\ requestedPumps > 2
                \/ oldLevel < THRESHOLDS["x8"] /\ THRESHOLDS["x8"] <= newLevel /\ requestedPumps > 3
          \/ /\requestedPumps' = requestedPumps + 1
             /\ \/ oldLevel >= THRESHOLDS["x7"] /\ THRESHOLDS["x7"] > newLevel /\ requestedPumps < 1
                \/ oldLevel >= THRESHOLDS["x6"] /\ THRESHOLDS["x6"]> newLevel /\ requestedPumps < 2
                \/ oldLevel >= THRESHOLDS["x4"] /\ THRESHOLDS["x4"] > newLevel /\ requestedPumps < 3
          \/ /\requestedPumps' = 4
             /\ \/ oldLevel < THRESHOLDS["x5"] /\ THRESHOLDS["x5"] <= newLevel /\ requestedPumps > 4
                \/ oldLevel >= THRESHOLDS["x3"] /\ THRESHOLDS["x3"] > newLevel
          \/ /\requestedPumps' = 5
             /\ \/ oldLevel >= THRESHOLDS["x2"] /\THRESHOLDS["x2"] > newLevel
                \/ oldLevel < THRESHOLDS["x1"] /\ THRESHOLDS["x1"] <= newLevel
          \/ /\requestedPumps' = 6
             /\newLevel < THRESHOLDS["x0"]
          \/ UNCHANGED <<states, requestedStates, requestedPumps, onp, ofp>>


activate(p) == /\IF (p >= 0 /\ p < 3)
                 THEN /\onp = p
                      /\onp' = (p + 1) % 3
                 ELSE onp' = onp
               /\states[p] = "OFF"
               /\requestedStates' = [requestedStates EXCEPT ![p] = "ON"]
               /\ UNCHANGED <<ofp>>

deactivate(p) == /\IF (p >= 0 /\ p < 3)
                   THEN /\ofp = p
                        /\ofp' = (p + 1) % 3
                   ELSE ofp' = ofp
                 /\states[p] = "ON"
                 /\requestedStates' = [requestedStates EXCEPT ![p] = "OFF"]
                 /\ UNCHANGED <<onp>>

selectPumps ==
  /\ \A p \in PUMPS : states[p] \notin {"STARTING", "STOPPING"}
  /\ defcon
  /\ Cardinality({p \in PUMPS : states[p] = "ON"}) # requestedPumps'
  /\ IF Cardinality({p \in PUMPS : states[p] = "ON"}) < requestedPumps'
     THEN \E p \in PUMPS : activate(p)
     ELSE \E p \in PUMPS : deactivate(p)

successON(p) == /\states' = [states EXCEPT ![p] = "ON"]
                /\ UNCHANGED <<requestedStates>>

failureON(p) == /\states' = [states EXCEPT ![p] = "DAMAGED"]
                /\requestedStates' = [requestedStates EXCEPT ![p] = "OFF"]

successOFF(p) == /\states' = [states EXCEPT ![p] = "OFF"]
                 /\ UNCHANGED <<requestedStates>>

failureOFF(p) == /\states' = [states EXCEPT ![p] = "DAMAGED"]
                 /\requestedStates' = [requestedStates EXCEPT ![p] = "ON"]

switchON(p) == /\states[p] = "OFF"
               /\requestedStates[p] = "ON"
               /\states' = [states EXCEPT ![p] = "STARTING"]
               /\ (successON(p) /\failureON(p))

switchOFF(p) == /\states[p] = "ON"
                /\requestedStates[p] = "OFF"
                /\states' = [states EXCEPT ![p] = "STOPING"]
                /\ (successOFF(p) /\failureOFF(p))

switchPumps == \E p \in PUMPS : switchON(p) /\switchOFF(p)

WPInit == /\states = [p \in PUMPS |-> "OFF"]
          /\requestedStates = [p \in PUMPS |-> "OFF"]
          /\onp = 0
          /\ofp = 0
          /\requestedPumps = 0
          /\ newLevel = 120
          /\ oldLevel = 120


WPNext == \/ newLevel' = newLevel-1 /\ oldLevel' = newLevel /\ UNCHANGED <<states, requestedStates, requestedPumps, onp, ofp>>
          \/ selectPumps /\ UNCHANGED <<oldLevel, newLevel, states>>
          \/ switchPumps /\ UNCHANGED <<oldLevel, newLevel, requestedPumps, onp, ofp>>
=============================================================================
\* Modification History
\* Last modified Mon Jul 13 19:32:28 BRT 2020 by gabriela
\* Created Wed Jun 10 07:11:49 BRT 2020 by gabriela
