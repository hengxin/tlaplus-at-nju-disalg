-------------------------- MODULE Linearizability --------------------------
CONSTANTS  Procs, Commands(_), Outputs(_), InitOutput(_), 
           ObjValues, InitObj, Apply(_, _, _)

ASSUME LinearAssumps == 
         /\ InitObj \in ObjValues
         /\ \A i \in Procs : InitOutput(i) \in Outputs(i)
         /\ \A i \in Procs : Outputs(i) \cap Commands(i) = { }
         /\ \A i \in Procs, obj \in ObjValues : 
              \A cmd \in Commands(i) : 
                  /\ Apply(i, cmd, obj).output \in Outputs(i)
                  /\ Apply(i, cmd, obj).newState \in ObjValues

VARIABLES object, interface, istate
vars == <<object, interface, istate>>

TypeOK == /\ object \in ObjValues
          /\ \A i \in Procs : /\ interface[i] \in Outputs(i) \cup Commands(i)
                              /\ istate[i] \in Outputs(i) \cup Commands(i)
          
Init == /\ object = InitObj
        /\ interface = [i \in Procs |-> InitOutput(i)]
        /\ istate = [i \in Procs |-> InitOutput(i)]
        
BeginOp(i, cmd) == /\ interface[i] \in Outputs(i)
                   /\ interface' = [interface EXCEPT ![i] = cmd]
                   /\ istate' = [istate EXCEPT ![i] = cmd]
                   /\ object' = object

DoOp(i) == /\ interface[i] \in Commands(i)
           /\ istate[i] = interface[i]
           /\ LET result == Apply(i, interface[i], object)
              IN  /\ object' = result.newState
                  /\ istate' = [istate EXCEPT ![i] = result.output]
           /\ interface' = interface
           
EndOp(i) == /\ interface[i] \in Commands(i)
            /\ istate[i] \in Outputs(i)
            /\ interface' = [interface EXCEPT ![i] = istate[i]]
            /\ UNCHANGED <<object, istate>> 

Next == \E i \in Procs : \/ \E cmd \in Commands(i) : BeginOp(i, cmd)
                         \/ DoOp(i) 
                         \/ EndOp(i)

SafeSpec == Init /\ [][Next]_vars  

Fairness == \A i \in Procs : WF_vars(DoOp(i)) /\ WF_vars(EndOp(i))  
Spec == SafeSpec /\ Fairness
=============================================================================
\* Modification History
\* Last modified Fri Oct 07 04:30:04 PDT 2016 by lamport
\* Created Tue Oct 04 02:01:02 PDT 2016 by lamport
