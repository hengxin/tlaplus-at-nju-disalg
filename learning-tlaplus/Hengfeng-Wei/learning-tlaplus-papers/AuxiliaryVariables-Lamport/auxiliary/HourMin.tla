------------------------------ MODULE HourMin -------------------------------
(***************************************************************************)
(* This module specifies a 24-hour clock displaying the hour h and the     *)
(* minute m, initially showing the time 00:00.                             *)
(***************************************************************************)
EXTENDS Integers
VARIABLES h, m

TypeOK == (h \in 0..23) /\ (m \in 0..59)

Init == (h=0) /\ (m=0)

Next == /\ m' = (m+1) % 60
        /\ h' = IF m' = 0 THEN (h+1) % 24
                          ELSE h
                          
Spec == Init /\ [][Next]_<<h,m>>
=============================================================================
\* Modification History
\* Last modified Thu Oct 20 05:48:46 PDT 2016 by lamport
\* Created Sun Oct 02 09:59:18 PDT 2016 by lamport
