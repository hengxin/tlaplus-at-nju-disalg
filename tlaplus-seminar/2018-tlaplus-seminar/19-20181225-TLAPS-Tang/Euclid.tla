------------------------------- MODULE Euclid -------------------------------
EXTENDS Integers, GCD, TLC, TLAPS \* TLAPS for PTL
CONSTANTS M, N

\*ASSUME /\ M \in Nat \ {0}
\*       /\ N \in Nat \ {0}

ASSUME MNPosInt == /\ M \in Nat \ {0}
                   /\ N \in Nat \ {0}

(****************************************************************************
--algorithm Euclid {
 variables x = M, y = N;
 { while (x # y) { if (x < y) { y := y - x }
                   else       { x := x - y }
                 };
 }
}
****************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = M
        /\ y = N
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x # y
               THEN /\ IF x < y
                          THEN /\ y' = y - x
                               /\ x' = x
                          ELSE /\ x' = x - y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

PartialCorrectness == (pc = "Done") => (x = y) /\ (x = GCD(M, N))

\*Inv == /\ GCD(x, y) = GCD(M, N)
\*       /\ (pc = "Done") => (x = y)

TypeOK == /\ x \in Nat \ {0}
          /\ y \in Nat \ {0}

Inv == /\ TypeOK
       /\ GCD(x, y) = GCD(M, N)
       /\ (pc = "Done") => (x = y)

\*THEOREM Spec => []PartialCorrectness
\*                <1>1. Init => Inv
\*                <1>2. Inv /\ [Next]_vars => Inv'
\*                <1>3. Inv => PartialCorrectness
\*                <1>4. QED

THEOREM Spec => []PartialCorrectness
                <1>1. Init => Inv
\*                  BY DEF Init, Inv, TypeOK
                  BY MNPosInt DEF Init, Inv, TypeOK
                <1>2. Inv /\ [Next]_vars => Inv'
                  BY MNPosInt, GCD2, GCD3 DEF Inv, TypeOK, Next, Lbl_1, vars
                <1>3. Inv => PartialCorrectness
                  BY MNPosInt, GCD1 DEF Inv, TypeOK, PartialCorrectness
                <1>4. QED
\*                  OBVIOUS
\*                  BY <1>1, <1>2, <1>3
\*                  BY <1>1, <1>2, <1>3 DEF Spec
                  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================
\* Modification History
\* Last modified Tue Dec 25 11:45:00 CST 2018 by tangruize
\* Created Tue Mar 20 16:24:59 CST 2018 by tangruize
