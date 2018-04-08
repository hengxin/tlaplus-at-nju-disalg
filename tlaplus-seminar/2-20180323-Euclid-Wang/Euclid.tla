PlusCal options (-termination)
------------------------------- MODULE Euclid -------------------------------
EXTENDS Naturals, TLC
CONSTANT N
gcd(x, y) == CHOOSE i \in 1..x :
                /\ x % i = 0
                /\ y % i = 0
                /\ \A j \in 1..x : /\ x % j = 0
                                   /\ y % j = 0
                                   => i >= j

(****************************************************
--algorithm EuclidAlg {
  variables u = 24 ; v \in 1..N ; v_ini = v ;
  {  \* print <<u, v>> ;
     while (u /= 0)
        { if (u < v) { u := v || v := u } ;
           u := u - v } ;
\*     print <<24, v_ini, "have gcd", v>>
     assert v = gcd(24, v_ini)
  }
}

*****************************************************)
\* BEGIN TRANSLATION
VARIABLES u, v, v_ini, pc

vars == << u, v, v_ini, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1..N
        /\ v_ini = v
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF u /= 0
               THEN /\ IF u < v
                          THEN /\ /\ u' = v
                                  /\ v' = u
                          ELSE /\ TRUE
                               /\ UNCHANGED << u, v >>
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(v = gcd(24, v_ini), 
                              "Failure of assertion at line 20, column 6.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << u, v >>
         /\ v_ini' = v_ini

Lbl_2 == /\ pc = "Lbl_2"
         /\ u' = u - v
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << v, v_ini >>

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Mar 27 21:35:43 CST 2018 by zfwang
\* Created Sat Mar 17 21:43:00 CST 2018 by zfwang



       
