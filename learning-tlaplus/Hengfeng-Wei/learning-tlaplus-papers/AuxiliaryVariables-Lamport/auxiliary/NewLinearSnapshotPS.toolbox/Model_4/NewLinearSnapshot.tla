------------------------- MODULE NewLinearSnapshot -------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Readers, Writers, RegVals, InitRegVal

ASSUME RdWrDisjoint == Readers  \cap Writers = {}

InitMem == [i \in Writers |-> InitRegVal]
MemVals == [Writers -> RegVals]
NotMemVal == CHOOSE v : v \notin MemVals
NotRegVal == CHOOSE v : v \notin RegVals

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
          
Init == /\ mem = InitMem
        /\ interface = [i \in Readers \cup Writers |->
                          IF i \in Readers THEN InitMem ELSE NotRegVal]
        /\ rstate = [i \in Readers |-> << >>]
        /\ wstate = [i \in Writers |-> NotRegVal]

BeginRd(i) == /\ interface[i] \in MemVals
              /\ interface' = [interface EXCEPT ![i] = NotMemVal]
              /\ rstate' = [rstate EXCEPT ![i] = <<mem>>]
              /\ UNCHANGED <<mem, wstate>>

BeginWr(i, cmd) == /\ interface[i] = NotRegVal
                   /\ interface' = [interface EXCEPT ![i] = cmd]
                   /\ wstate' = [wstate EXCEPT ![i] = cmd]
                   /\ UNCHANGED <<mem, rstate>>

          
DoWr(i) == /\ interface[i] \in RegVals
           /\ wstate[i] = interface[i]
           /\ mem' = [mem EXCEPT ![i] = interface[i]]
           /\ wstate' = [wstate EXCEPT ![i] = NotRegVal]
           /\ rstate' = [r \in Readers |-> 
                            IF rstate[r] = << >>
                              THEN << >>
                              ELSE Append(rstate[r], mem')]
           /\ interface' = interface

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

Fairness == /\ \A i \in Readers : WF_vars(EndRd(i))
            /\ \A i \in Writers : WF_vars(DoWr(i)) /\ WF_vars(EndWr(i))
                    
Spec == Init /\ [][Next]_vars /\ Fairness   
SafeSpec ==  Init /\ [][Next]_vars
====================================================
(***************************************************************************)
(* The following uncommented and used to check Condition                   *)
(***************************************************************************)     
Pi == Nat \ {0}
Dom == {r \in Readers : rstate[r] # << >>}
INSTANCE Prophecy WITH DomPrime <- Dom'

IEndRd(i, j) == /\ interface[i] = NotMemVal
                /\ interface' = [interface EXCEPT ![i] = rstate[i][j]]
                /\ rstate' = [rstate EXCEPT ![i] = << >>]
                /\ UNCHANGED <<mem, wstate>>

Nxt == \/ \E i \in Readers : \/ BeginRd(i)  
                             \/ \E j \in 1..Len(rstate[i]) : IEndRd(i, j)
       \/ \E i \in Writers : \/ \E cmd \in RegVals : BeginWr(i, cmd)
                             \/ DoWr(i) \/ EndWr(i)

THEOREM Next = Nxt
BY DEF Next, Nxt, EndRd, IEndRd

PredBeginRd(p) == TRUE
PredDomBeginRd == {}
DomInjBeginRd  == IdFcn(Dom)

PredIEndRd(p, i, j) == j = p[i]
PredDomIEndRd(i) == {i}
DomInjIEndRd  == IdFcn(Dom')

PredBeginWr(p) == TRUE
PredDomBeginWr == {}
DomInjBeginWr  == IdFcn(Dom)

PredDoWr(p) == TRUE
PredDomDoWr == {}
DomInjDoWr  == IdFcn(Dom)

PredEndWr(p) == TRUE
PredDomEndWr == {}
DomInjEndWr  == IdFcn(Dom)

Condition ==
 [][ 
     /\ \A i \in Readers :
          /\ ProphCondition(BeginRd(i), DomInjBeginRd, PredDomBeginRd,
                            PredBeginRd)
          /\ \A j \in 1..Len(rstate[i]) :
                ProphCondition(IEndRd(i, j), DomInjIEndRd, 
                               PredDomIEndRd(i),
                               LAMBDA p : PredIEndRd(p, i, j)
                               )
     /\ \A i \in Writers :
          /\ \A cmd \in RegVals :
                ProphCondition(BeginWr(i, cmd), DomInjBeginWr, PredDomBeginWr,
                               PredBeginWr)
          /\ ProphCondition(DoWr(i), DomInjDoWr, PredDomDoWr, PredDoWr)
          /\ ProphCondition(EndWr(i), DomInjEndWr, PredDomEndWr, PredEndWr)
   ]_vars                   
=============================================================================
\* Modification History
\* Last modified Wed Oct 05 09:46:31 PDT 2016 by lamport
\* Created Wed Oct 05 01:23:41 PDT 2016 by lamport
