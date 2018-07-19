-------------------------- MODULE NewLinearSnapshot -------------------------
(***************************************************************************)
(* This module is part of the AfekSimplified example in Section 6 of the   *)
(* paper "Auxiliary Variables in TLA+".  It is equivalent to the           *)
(* specification in module LinearSnapshot of a linearizable snapshot       *)
(* algorithm, in the sense that it permits the same behaviors of the       *)
(* externally visible variable `interface'.  You should understand that    *)
(* specification before reading this module.                               *)
(*                                                                         *)
(* This specification differs from the one in LinearSnapshot by deferring  *)
(* the choice of a reader's output as long as possible--namely, the choice *)
(* is made only in the EndRd action.  The reader maintains a list of all   *)
(* the values that the memory mem had while the read operation is being    *)
(* performed, and has the EndRd action choose an arbitrary element of that *)
(* list to return as the output.                                           *)
(*                                                                         *)
(* The equivalence of the two linearizable snapshot algorithms means that  *)
(* if Spec_NL is formula Spec of this module and Spec_L is formula Spec of *)
(* module LinearSnapshot, then \EE mem, rstate, wstate : Spec_NL is        *)
(* equivalent to \EE mem, istate : Spec_L.  We only show that the first    *)
(* implies the second, since that is all we need for our example of the    *)
(* simplified Afek et al. snapshot algorithm.                              *)
(***************************************************************************)
EXTENDS Integers, Sequences

(***************************************************************************)
(* The declared and defined constants are the same as in module            *)
(* LinearSnapshot.                                                         *)
(***************************************************************************)
CONSTANTS Readers, Writers, RegVals, InitRegVal

ASSUME /\ Readers \cap Writers = {}
       /\ InitRegVal \in RegVals

InitMem == [i \in Writers |-> InitRegVal]
MemVals == [Writers -> RegVals]
NotMemVal == CHOOSE v : v \notin MemVals
NotRegVal == CHOOSE v : v \notin RegVals

(***************************************************************************)
(* The variables mem and `interface' are the same as in LinearSnapshot.    *)
(* The variable wstate is a function with domain Writers, where wstate[i]  *)
(* assumes the same value as istate[i] does for the LinearSnapshot spec,   *)
(* for all i \in Writers.  The variable rstate is a function with domain   *)
(* `Readers' such that rstate[i] = << >> when reader i is not performing a *)
(* read operation, and while performing a read it equals the sequence of   *)
(* values that mem has assumed since the BeginRd(i) step.                  *)
(*                                                                         *)
(* We will not bother explaining the assertions that the spec makes about  *)
(* mem, `interface', and wstate, since they are exactly the same as in     *)
(* LinearSnapshot for mem and `interface', and every condition on          *)
(* wstate[i] is the same as the corresponding condition on istate[i] in    *)
(* LinearSnapshot, for i \in Writers.                                      *)
(***************************************************************************)
VARIABLES mem, interface, rstate, wstate
vars == <<mem, interface, rstate, wstate>>

TypeOK == /\ mem \in MemVals
          /\ /\ DOMAIN interface = Readers \cup Writers
             /\ \A i \in Readers : interface[i] \in MemVals \cup {NotMemVal}
             /\ \A i \in Writers : interface[i] \in RegVals \cup {NotRegVal}
          /\ /\ rstate \in [Readers -> Seq(MemVals)]
             /\ \A i \in Readers : 
                    (rstate[i] = << >>) <=> (interface[i] \in MemVals)
          /\ wstate \in [Writers -> RegVals \cup {NotRegVal}]

(***************************************************************************)
(* Since no reader is initially executing a read command, rstate[i]        *)
(* initially equals the empty sequence for each reader i.                  *)
(***************************************************************************)          
Init == /\ mem = InitMem
        /\ interface = [i \in Readers \cup Writers |->
                          IF i \in Readers THEN InitMem ELSE NotRegVal]
        /\ rstate = [i \in Readers |-> << >>]
        /\ wstate = [i \in Writers |-> NotRegVal]

(***************************************************************************)
(* Since they leave rstate unchanged, BeginWr and EndWr are the same as in *)
(* LinearSnapshot.                                                         *)
(***************************************************************************)
BeginWr(i, cmd) == /\ interface[i] = NotRegVal
                   /\ interface' = [interface EXCEPT ![i] = cmd]
                   /\ wstate' = [wstate EXCEPT ![i] = cmd]
                   /\ UNCHANGED <<mem, rstate>>

(***************************************************************************)
(* The BeginRd(i) action sets rstate[i] to <<mem>>, since the current      *)
(* value of mem is the only output value EndRd(i) can return if executed   *)
(* immediately afterwards.                                                 *)
(***************************************************************************)
BeginRd(i) == /\ interface[i] \in MemVals
              /\ interface' = [interface EXCEPT ![i] = NotMemVal]
              /\ rstate' = [rstate EXCEPT ![i] = <<mem>>]
              /\ UNCHANGED <<mem, wstate>>
              
(***************************************************************************)
(* The DoWr(i) action appends the new value of mem to rstate[j] for each   *)
(* reader j currently performing a read operation, since each of those     *)
(* readers can return that value as their output.                          *)
(***************************************************************************)         
DoWr(i) == /\ interface[i] \in RegVals
           /\ wstate[i] = interface[i]
           /\ mem' = [mem EXCEPT ![i] = interface[i]]
           /\ wstate' = [wstate EXCEPT ![i] = NotRegVal]
           /\ rstate' = [j \in Readers |-> 
                            IF rstate[j] = << >>
                              THEN << >>
                              ELSE Append(rstate[j], mem')]
           /\ interface' = interface

(***************************************************************************)
(* EndRd(i) can set as its output any element of rstate[i].  It resets     *)
(* rstate[i] to the empty sequence.                                        *)
(***************************************************************************)
EndRd(i) == /\ interface[i] = NotMemVal
            /\ \E j \in 1..Len(rstate[i]) :
                   interface' = [interface EXCEPT ![i] = rstate[i][j]]
            /\ rstate' = [rstate EXCEPT ![i] = << >>]
            /\ UNCHANGED <<mem, wstate>> 

EndWr(i) == /\ interface[i] \in RegVals
            /\ wstate[i] = NotRegVal
            /\ interface' = [interface EXCEPT ![i] = wstate[i]]
            /\ UNCHANGED <<mem, rstate, wstate>> 

Next == \/ \E i \in Readers : BeginRd(i) \/ EndRd(i)
        \/ \E i \in Writers : \/ \E cmd \in RegVals : BeginWr(i, cmd)
                              \/ DoWr(i) \/ EndWr(i)

SafeSpec ==  Init /\ [][Next]_vars

(***************************************************************************)
(* The fairness condition implies that every read or write operation that  *)
(* has begun must eventually finish.                                       *)
(***************************************************************************)
Fairness == /\ \A i \in Readers : WF_vars(EndRd(i))
            /\ \A i \in Writers : WF_vars(DoWr(i)) /\ WF_vars(EndWr(i))
                    
Spec == Init /\ [][Next]_vars /\ Fairness   
=============================================================================
\* Modification History
\* Last modified Sat Oct 22 01:41:33 PDT 2016 by lamport
\* Created Wed Oct 05 01:23:41 PDT 2016 by lamport
