------------------------------ MODULE HourMin -------------------------------
EXTENDS Integers
VARIABLES h, m

Init == (h=0) /\ (m=0)

Next == /\ m' = (m+1) % 60
        /\ h' = IF m' = 0 THEN (h+1) % 24
                          ELSE h
                          
Spec == Init /\ [][Next]_<<h,m>>
Spec2 == (h=0) /\ (m=59) /\ [][Next]_<<h,m>>
=============================================================================
\* Modification History
\* Last modified Wed Oct 12 06:00:15 PDT 2016 by lamport
\* Created Sun Oct 02 09:59:18 PDT 2016 by lamport
