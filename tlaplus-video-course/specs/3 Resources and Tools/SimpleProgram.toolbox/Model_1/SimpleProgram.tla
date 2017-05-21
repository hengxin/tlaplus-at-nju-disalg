--------------------------- MODULE SimpleProgram ---------------------------
EXTENDS Integers
VARIABLES i, pc   

Init == (pc = "start") /\ (i = 0)

Pick == /\ pc = "start"  
        /\ i' \in 0..1000
        /\ pc' = "middle"

Add1 == /\ pc = "middle" 
        /\ i' = i + 1
        /\ pc' = "done"  
           
Next == Pick \/ Add1
=============================================================================
\* Modification History
\* Last modified Sun May 21 15:30:37 CST 2017 by ics-ant
\* Created Sun May 21 15:28:54 CST 2017 by ics-ant
