------------------------------ MODULE hystrix ------------------------------
EXTENDS Naturals, TLC

(* --algorithm HystrixCircuit {
variables failures = 0,
          maxFailures \in 0..5,
          state = "closed",
          states = {"closed", "open"},
          subStates = {"up", "down"},
          subState \in subStates,
          time = 0,
          retryTime \in 1..5,
    {
        HYX_PROCESSING: 
        while (TRUE) {
            HYX_CHECK_CLOSED_CIRCUIT: 
            if (state = "closed") {
                if (subState = "up") {
                    HYX_RESET_FAILURES: failures := 0;
                } else {
                    HYX_INCREMENT_FAILURE: failures := failures + 1;
                };
            } 
            HYX_CHECK_OPEN_CIRCUIT: else { 
                
            };
            HYX_CHECK_FAILURES: if (failures >= maxFailures) {
                HYX_OPEN: state := "open";
            };
        };
    }
}
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES failures, maxFailures, state, states, subStates, subState, pc

vars == << failures, maxFailures, state, states, subStates, subState, pc >>

Init == (* Global variables *)
        /\ failures = 0
        /\ maxFailures \in 0..5
        /\ state = "closed"
        /\ states = {"closed", "open"}
        /\ subStates = {"up", "down"}
        /\ subState \in subStates
        /\ pc = "HYX_PROCESSING"

HYX_PROCESSING == /\ pc = "HYX_PROCESSING"
                  /\ pc' = "HYX_CHECK_CIRCUIT"
                  /\ UNCHANGED << failures, maxFailures, state, states, 
                                  subStates, subState >>

HYX_CHECK_CIRCUIT == /\ pc = "HYX_CHECK_CIRCUIT"
                     /\ IF state = "closed"
                           THEN /\ IF subState = "up"
                                      THEN /\ pc' = "HYX_RESET_FAILURES"
                                      ELSE /\ pc' = "HYX_INCREMENT_FAILURE"
                           ELSE /\ pc' = "HYX_CHECK_FAILURES"
                     /\ UNCHANGED << failures, maxFailures, state, states, 
                                     subStates, subState >>

HYX_RESET_FAILURES == /\ pc = "HYX_RESET_FAILURES"
                      /\ failures' = 0
                      /\ pc' = "HYX_CHECK_FAILURES"
                      /\ UNCHANGED << maxFailures, state, states, subStates, 
                                      subState >>

HYX_INCREMENT_FAILURE == /\ pc = "HYX_INCREMENT_FAILURE"
                         /\ failures' = failures + 1
                         /\ pc' = "HYX_CHECK_FAILURES"
                         /\ UNCHANGED << maxFailures, state, states, subStates, 
                                         subState >>

HYX_CHECK_FAILURES == /\ pc = "HYX_CHECK_FAILURES"
                      /\ IF failures >= maxFailures
                            THEN /\ pc' = "HYX_OPEN"
                            ELSE /\ pc' = "HYX_PROCESSING"
                      /\ UNCHANGED << failures, maxFailures, state, states, 
                                      subStates, subState >>

HYX_OPEN == /\ pc = "HYX_OPEN"
            /\ state' = "open"
            /\ pc' = "HYX_PROCESSING"
            /\ UNCHANGED << failures, maxFailures, states, subStates, subState >>

Next == HYX_PROCESSING \/ HYX_CHECK_CIRCUIT \/ HYX_RESET_FAILURES
           \/ HYX_INCREMENT_FAILURE \/ HYX_CHECK_FAILURES \/ HYX_OPEN

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

HyxOK == /\ state \in states
         /\ subState \in subStates

=============================================================================
\* Modification History
\* Last modified Mon Nov 27 19:55:32 PST 2017 by gaffo
\* Created Mon Nov 27 15:46:58 PST 2017 by gaffo
