------------------------------ MODULE hystrix ------------------------------
EXTENDS Naturals, TLC

(* --algorithm HystrixCircuit {
variables failures = 0,
          maxFailures \in 0..5,
    {

        A: alice_account := alice_account - money;
        B: bob_account := bob_account + money;
    }
}
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES alice_account, bob_account, money, pc

vars == << alice_account, bob_account, money, pc >>

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ money = 5
        /\ pc = "A"

A == /\ pc = "A"
     /\ alice_account' = alice_account - money
     /\ pc' = "B"
     /\ UNCHANGED << bob_account, money >>

B == /\ pc = "B"
     /\ bob_account' = bob_account + money
     /\ pc' = "Done"
     /\ UNCHANGED << alice_account, money >>

Next == A \/ B
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Mon Nov 27 16:09:03 PST 2017 by gaffo
\* Created Mon Nov 27 15:46:58 PST 2017 by gaffo
