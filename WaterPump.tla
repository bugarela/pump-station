----------------------------- MODULE WaterPump -----------------------------
EXTENDS Integers, FiniteSets

CONSTANT PUMPS, THRESHOLDS

VARIABLES states, requestedStates, requestedPumps, onp, ofp, level

defcon == requestedPumps = CASE level' > THRESHOLDS["n"] -> 0
  [] (level < THRESHOLDS["11"] /\ THRESHOLDS["11"] <= level') \/(level < THRESHOLDS["10"] /\THRESHOLDS["10"] <= level' /\ requestedPumps' > 1) \/(level < THRESHOLDS["9"] /\ THRESHOLDS["9"] <= level' /\ requestedPumps' > 2)  \/(level < THRESHOLDS["8"] /\ THRESHOLDS["8"] <= level' /\ requestedPumps' > 3)-> requestedPumps' - 1
  [] (level >= THRESHOLDS["7"] /\ THRESHOLDS["7"] > level' /\ requestedPumps' < 1) \/(level >= THRESHOLDS["6"] /\ THRESHOLDS["6"]> level' /\ requestedPumps' < 2) \/(level >= THRESHOLDS["4"] /\ THRESHOLDS["4"] > level' /\ requestedPumps' < 3) -> requestedPumps' + 1
  [] (level < THRESHOLDS["5"] /\ THRESHOLDS["5"] <= level' /\ requestedPumps' > 4)  \/(level >= THRESHOLDS["3"] /\ THRESHOLDS["3"]> level') -> 4
  [] (level >= THRESHOLDS["2"] /\THRESHOLDS["11"] > level') /\ (level < THRESHOLDS["1"] /\ THRESHOLDS["1"] <= level') -> 5
  [] level' < THRESHOLDS["0"] -> 6


activate(p) == /\IF (p >= 0 /\ p < 3)
                 THEN /\onp = p
                      /\onp' = (p + 1) % 3
                 ELSE onp' = onp
               /\states[p] = "OFF"
               /\requestedStates' = [requestedStates EXCEPT ![p] = "ON"]

deactivate(p) == /\IF (p >= 0 /\ p < 3)
                   THEN /\ofp = p
                        /\ofp' = (p + 1) % 3
                   ELSE ofp' = ofp
                 /\states[p] = "ON"
                 /\requestedStates' = [requestedStates EXCEPT ![p] = "OFF"]

selectPumps ==
  /\ \A p \in PUMPS : states[p] \in {"STARTING", "STOPPING"}
  /\defcon
  /\ IF Cardinality({p \in PUMPS : states[p] = "ON"}) < requestedPumps'
     THEN \E p \in PUMPS : activate(p)
     ELSE \E p \in PUMPS : deactivate(p)

successON(p) == /\states' = [states EXCEPT ![p] = "ON"]

failureON(p) == /\states' = [states EXCEPT ![p] = "DAMAGED"]
                /\requestedStates' = [requestedStates EXCEPT ![p] = "OFF"]

successOFF(p) == /\states' = [states EXCEPT ![p] = "OFF"]

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

WPNext == selectPumps /\switchPumps
=============================================================================
\* Modification History
\* Last modified Sun Jul 12 11:43:01 BRT 2020 by gabriela
\* Created Wed Jun 10 07:11:49 BRT 2020 by gabriela
