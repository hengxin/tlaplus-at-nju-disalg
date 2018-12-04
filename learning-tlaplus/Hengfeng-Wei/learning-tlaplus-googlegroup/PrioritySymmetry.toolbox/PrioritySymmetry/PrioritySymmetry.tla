-------------------------- MODULE PrioritySymmetry --------------------------
EXTENDS Naturals, Reals, FiniteSets, AdditionalFunctionOperators

CONSTANTS Client,    \* the set of clients
          N

Priority == CHOOSE f \in [Client -> 1 .. Cardinality(Client)] : Injective(f)

(***************************************************************************
--algorithm Foo {
   variable x \in Client;
   { x := (N - Priority[x])
   }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in Client
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ x' = (N - Priority[x])
         /\ pc' = "Done"

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Mon Dec 03 13:53:10 CST 2018 by hengxin
\* Created Mon Dec 03 10:49:05 CST 2018 by hengxin
