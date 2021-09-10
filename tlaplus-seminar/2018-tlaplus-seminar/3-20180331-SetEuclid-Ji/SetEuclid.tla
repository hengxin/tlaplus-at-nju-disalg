----------------------------- MODULE SetEuclid -----------------------------
EXTENDS Integers,FiniteSets ,GCD
CONSTANTS Input
ASSUME  /\ Input \subseteq Nat \{0}
        /\ Input # {}
        /\ IsFiniteSet(Input)

(****************************************************
--fair algorithm SetEuclid {
variable S = Input;
{
    while ( Cardinality(S) > 1 )
        { with ( x \in S, y \in {s \in S : s > x} )
         {S := (S \{y}) \cup { y -x} }
         }
         }
} 
 *****************************************************)
\* BEGIN TRANSLATION
VARIABLES S, pc

RECURSIVE SetSum(_)
SetSum(T) == IF T = {} THEN 0
                       ELSE LET t == CHOOSE x \in T : TRUE
                            IN  t + SetSum(T \ {t})
vars == << S, pc >>

Init == (* Global variables *)
        /\ S = Input
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Cardinality(S) > 1
               THEN /\ \E x \in S:
                         \E y \in {s \in S : s > x}:
                           S' = ((S \{y}) \cup { y -x})
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ S' = S

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
PartialCorrectness == (pc = "Done") => (S = {SetGCD(Input)})
=============================================================================
\* Modification History
\* Last modified Mon Mar 26 21:41:30 CST 2018 by xhdn
\* Created Mon Mar 26 10:46:12 CST 2018 by xhdn
