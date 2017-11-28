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
          running = TRUE,
    {
        HYX_PROCESSING: 
        while (running) { 
            if (state = "closed") {
                HYX_CHECK_CLOSED_CIRCUIT:
                if (subState = "up") {
                    HYX_RESET_FAILURES: failures := 0;
                } else {
                    HYX_INCREMENT_FAILURE: failures := failures + 1;
                    HYX_CHECK_FAILURES: if (failures >= maxFailures) {
                        HYX_OPEN: state := "open";
                    };
                };
            } else {
                HYX_CHECK_OPEN_CIRCUIT: 
                time := time + 1;
                if (time >= retryTime) {
                    HYX_OPEN_TIMER_FIRED:
                    if (subState = "up") {
                        HYX_TRY_TIMER:
                        state := "closed";
                        time := 0;
                        running := FALSE;
                    } 
                    else {
                        HYX_OPEN_RESET_TIMER: 
                        time := 0;
                    };
                };
            };
        };
    }
}
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES failures, maxFailures, state, states, subStates, subState, time, 
          retryTime, running, pc

vars == << failures, maxFailures, state, states, subStates, subState, time, 
           retryTime, running, pc >>

Init == (* Global variables *)
        /\ failures = 0
        /\ maxFailures \in 0..5
        /\ state = "closed"
        /\ states = {"closed", "open"}
        /\ subStates = {"up", "down"}
        /\ subState \in subStates
        /\ time = 0
        /\ retryTime \in 1..5
        /\ running = TRUE
        /\ pc = "HYX_PROCESSING"

HYX_PROCESSING == /\ pc = "HYX_PROCESSING"
                  /\ IF running
                        THEN /\ IF state = "closed"
                                   THEN /\ pc' = "HYX_CHECK_CLOSED_CIRCUIT"
                                   ELSE /\ pc' = "HYX_CHECK_OPEN_CIRCUIT"
                        ELSE /\ pc' = "Done"
                  /\ UNCHANGED << failures, maxFailures, state, states, 
                                  subStates, subState, time, retryTime, 
                                  running >>

HYX_CHECK_CLOSED_CIRCUIT == /\ pc = "HYX_CHECK_CLOSED_CIRCUIT"
                            /\ IF subState = "up"
                                  THEN /\ pc' = "HYX_RESET_FAILURES"
                                  ELSE /\ pc' = "HYX_INCREMENT_FAILURE"
                            /\ UNCHANGED << failures, maxFailures, state, 
                                            states, subStates, subState, time, 
                                            retryTime, running >>

HYX_RESET_FAILURES == /\ pc = "HYX_RESET_FAILURES"
                      /\ failures' = 0
                      /\ pc' = "HYX_PROCESSING"
                      /\ UNCHANGED << maxFailures, state, states, subStates, 
                                      subState, time, retryTime, running >>

HYX_INCREMENT_FAILURE == /\ pc = "HYX_INCREMENT_FAILURE"
                         /\ failures' = failures + 1
                         /\ pc' = "HYX_CHECK_FAILURES"
                         /\ UNCHANGED << maxFailures, state, states, subStates, 
                                         subState, time, retryTime, running >>

HYX_CHECK_FAILURES == /\ pc = "HYX_CHECK_FAILURES"
                      /\ IF failures >= maxFailures
                            THEN /\ pc' = "HYX_OPEN"
                            ELSE /\ pc' = "HYX_PROCESSING"
                      /\ UNCHANGED << failures, maxFailures, state, states, 
                                      subStates, subState, time, retryTime, 
                                      running >>

HYX_OPEN == /\ pc = "HYX_OPEN"
            /\ state' = "open"
            /\ pc' = "HYX_PROCESSING"
            /\ UNCHANGED << failures, maxFailures, states, subStates, subState, 
                            time, retryTime, running >>

HYX_CHECK_OPEN_CIRCUIT == /\ pc = "HYX_CHECK_OPEN_CIRCUIT"
                          /\ time' = time + 1
                          /\ IF time' >= retryTime
                                THEN /\ pc' = "HYX_OPEN_TIMER_FIRED"
                                ELSE /\ pc' = "HYX_PROCESSING"
                          /\ UNCHANGED << failures, maxFailures, state, states, 
                                          subStates, subState, retryTime, 
                                          running >>

HYX_OPEN_TIMER_FIRED == /\ pc = "HYX_OPEN_TIMER_FIRED"
                        /\ IF subState = "up"
                              THEN /\ pc' = "HYX_TRY_TIMER"
                              ELSE /\ pc' = "HYX_OPEN_RESET_TIMER"
                        /\ UNCHANGED << failures, maxFailures, state, states, 
                                        subStates, subState, time, retryTime, 
                                        running >>

HYX_TRY_TIMER == /\ pc = "HYX_TRY_TIMER"
                 /\ state' = "closed"
                 /\ time' = 0
                 /\ running' = FALSE
                 /\ pc' = "HYX_PROCESSING"
                 /\ UNCHANGED << failures, maxFailures, states, subStates, 
                                 subState, retryTime >>

HYX_OPEN_RESET_TIMER == /\ pc = "HYX_OPEN_RESET_TIMER"
                        /\ time' = 0
                        /\ pc' = "HYX_PROCESSING"
                        /\ UNCHANGED << failures, maxFailures, state, states, 
                                        subStates, subState, retryTime, 
                                        running >>

Next == HYX_PROCESSING \/ HYX_CHECK_CLOSED_CIRCUIT \/ HYX_RESET_FAILURES
           \/ HYX_INCREMENT_FAILURE \/ HYX_CHECK_FAILURES \/ HYX_OPEN
           \/ HYX_CHECK_OPEN_CIRCUIT \/ HYX_OPEN_TIMER_FIRED \/ HYX_TRY_TIMER
           \/ HYX_OPEN_RESET_TIMER
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

HyxOK == /\ state \in states
         /\ subState \in subStates

=============================================================================
\* Modification History
\* Last modified Mon Nov 27 21:06:07 PST 2017 by gaffo
\* Created Mon Nov 27 15:46:58 PST 2017 by gaffo
