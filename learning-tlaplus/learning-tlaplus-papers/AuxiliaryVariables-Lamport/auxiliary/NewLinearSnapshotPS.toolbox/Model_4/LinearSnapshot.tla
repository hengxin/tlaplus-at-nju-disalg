--------------------------- MODULE LinearSnapshot ---------------------------
CONSTANTS Readers, Writers, RegVals, InitRegVal

ASSUME /\ Readers  \cap Writers = {}
       /\ InitRegVal \in RegVals

Procs == Readers \cup Writers

MemVals == [Writers -> RegVals]
InitMem == [i \in Writers |-> InitRegVal]

NotMemVal == CHOOSE v : v \notin MemVals
NotRegVal == CHOOSE v : v \notin RegVals

Commands(i) == IF i \in Readers THEN {NotMemVal}
                                ELSE RegVals

Outputs(i) == IF i \in Readers THEN MemVals 
                               ELSE {NotRegVal}

InitOutput(i) == IF i \in Readers THEN InitMem ELSE NotRegVal  

       
Apply(i, cmd, obj) == IF i \in Readers 
                          THEN [newState |-> obj, output |-> obj]
                          ELSE [newState |-> [obj EXCEPT ![i] = cmd],
                                output |-> NotRegVal]
VARIABLES mem, interface, istate

INSTANCE Linearizability WITH ObjValues <- MemVals, InitObj <- InitMem,  
                              object <- mem

ASSUME LinearAssumps
\* ============================================================================
BeginRd(i) == /\ interface[i] \in MemVals
              /\ interface' = [interface EXCEPT ![i] = NotMemVal]
              /\ istate' = [istate EXCEPT ![i] = NotMemVal]
              /\ mem' = mem

BeginWr(i, cmd) == /\ interface[i] = NotRegVal
                   /\ interface' = [interface EXCEPT ![i] = cmd]
                   /\ istate' = [istate EXCEPT ![i] = cmd]
                   /\ mem' = mem
                   
DoRd(i) == /\ interface[i] = NotMemVal
           /\ istate[i] = NotMemVal
           /\ LET result == Apply(i, NotMemVal, mem)
              IN  /\ mem' = result.newState
                  /\ istate' = [istate EXCEPT ![i] = result.output]
           /\ interface' = interface

DoWr(i) == /\ interface[i] \in RegVals
           /\ istate[i] = interface[i]
           /\ LET result == Apply(i, interface[i], mem)
              IN  /\ mem' = result.newState
                  /\ istate' = [istate EXCEPT ![i] = result.output]
           /\ interface' = interface

EndRd(i) == /\ interface[i] = NotMemVal
            /\ istate[i] \in MemVals
            /\ interface' = [interface EXCEPT ![i] = istate[i]]
            /\ UNCHANGED <<mem, istate>> 

EndWr(i) == /\ interface[i] \in RegVals
            /\ istate[i] \in Outputs(i)
            /\ interface' = [interface EXCEPT ![i] = istate[i]]
            /\ UNCHANGED <<mem, istate>> 

Nxt == \/ \E i \in Readers : BeginRd(i) \/ DoRd(i) \/ EndRd(i)
       \/ \E i \in Writers : \/ \E cmd \in RegVals : BeginWr(i, cmd)
                             \/ DoWr(i) \/ EndWr(i)

THEOREM ASSUME Readers  \cap Writers = {}
        PROVE  Next = Nxt
BY DEF Next, Nxt, BeginOp, EndOp, DoOp, BeginRd, EndRd, DoRd, BeginWr, 
       EndWr, DoWr, Procs, Commands, Outputs, InitOutput, Apply
=============================================================================
\* Modification History
\* Last modified Fri Oct 07 08:00:27 PDT 2016 by lamport
\* Created Tue Oct 04 02:26:20 PDT 2016 by lamport
