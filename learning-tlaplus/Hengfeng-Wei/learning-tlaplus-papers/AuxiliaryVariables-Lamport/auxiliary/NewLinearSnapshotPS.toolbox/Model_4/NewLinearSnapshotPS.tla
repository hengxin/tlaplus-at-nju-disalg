------------------------ MODULE NewLinearSnapshotPS ------------------------
EXTENDS NewLinearSnapshot

(***************************************************************************)
(* Adding the prophecy variable p.                                         *)
(***************************************************************************)
Pi == Nat \ {0}
Dom == {r \in Readers : rstate[r] # << >>}
INSTANCE Prophecy WITH DomPrime <- Dom'

IEndRd(i, j) == /\ interface[i] = NotMemVal
                /\ interface' = [interface EXCEPT ![i] = rstate[i][j]]
                /\ rstate' = [rstate EXCEPT ![i] = << >>]
                /\ UNCHANGED <<mem, wstate>>

Nxt == \/ \E i \in Readers : \/ BeginRd(i)  
                             \/ \E j \in 1..Len(rstate[i]) : IEndRd(i,j)
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
 [][ /\ \A i \in Readers :
          /\ ProphCondition(BeginRd(i), DomInjBeginRd, PredDomBeginRd,
                            PredBeginRd)
          /\ \A j \in 1..Len(rstate[i]) :
                ProphCondition(IEndRd(i, j), DomInjIEndRd, 
                               PredDomIEndRd(i),
                               LAMBDA p : PredIEndRd(p, i, j))
     /\ \A i \in Writers :
          /\ \A cmd \in RegVals :
                ProphCondition(BeginWr(i, cmd), DomInjBeginWr, PredDomBeginWr,
                               PredBeginWr)
          /\ ProphCondition(DoWr(i), DomInjDoWr, PredDomDoWr, PredDoWr)
          /\ ProphCondition(EndWr(i), DomInjEndWr, PredDomEndWr, PredEndWr)
   ]_vars

VARIABLE p
varsP == <<vars, p>>

TypeOKP == TypeOK /\ (p \in [Dom -> Pi])
InitP == Init /\ (p = EmptyFcn)

BeginRdP(i) == ProphAction(BeginRd(i), p, p', DomInjBeginRd,  
                           PredDomBeginRd, PredBeginRd)

BeginWrP(i, cmd) == ProphAction(BeginWr(i, cmd), p, p', DomInjBeginWr,  
                                PredDomBeginWr, PredBeginWr)
          
DoWrP(i) == ProphAction(DoWr(i), p, p', DomInjDoWr, PredDomDoWr, PredDoWr)

IEndRdP(i, j) == ProphAction(IEndRd(i, j),  p, p', DomInjIEndRd, 
                             PredDomIEndRd(i), LAMBDA q : PredIEndRd(q, i, j))

EndWrP(i) == ProphAction(EndWr(i), p, p', DomInjEndWr, PredDomEndWr, PredEndWr)

NextP == \/ \E i \in Readers : \/ BeginRdP(i)  
                               \/ \E j \in 1..Len(rstate[i]) : IEndRdP(i,j)
         \/ \E i \in Writers : \/ \E cmd \in RegVals : BeginWrP(i, cmd)
                               \/ DoWrP(i) \/ EndWrP(i)

SpecP == InitP /\ [][NextP]_varsP /\ Fairness
-----------------------------------------------------------------------------
\*VARIABLE h
\*varsPH == <<vars, p, h>>
\*TypeOKPH == TypeOKP /\ (h \in [Writers -> SUBSET Readers])
\*InitPH == InitP /\ (h = [i \in Writers |-> {}])
\*
\*BeginRdPH(i)       == BeginRdP(i) /\ (h' = h)
\*BeginWrPH(i, cmd)  == BeginWrP(i, cmd) /\ (h' = h)
\*DoWrPH(i)          == /\ DoWrP(i) 
\*                      /\ h' = [h EXCEPT ![i] = 
\*                                 {j \in Readers : 
\*                                  (rstate[j] # << >>) /\ (p[j] = Len(rstate'[j]))}]
\*IEndRdPH(i, j)     == IEndRdP(i, j) /\ (h' = h)
\*EndWrPH(i)         == EndWrP(i) /\ (h' = [h EXCEPT ![i] = {}])
\*
\*NextPH == \/ \E i \in Readers : \/ BeginRdPH(i)  
\*                                \/ \E j \in 1..Len(rstate[i]) : IEndRdPH(i,j)
\*          \/ \E i \in Writers : \/ \E cmd \in RegVals : BeginWrPH(i, cmd)
\*                                \/ DoWrPH(i) \/ EndWrPH(i)
\*
\*SpecPH == InitPH /\ [][NextPH]_varsPH /\ Fairness
-----------------------------------------------------------------------------

top == [id |-> "None"] 
VARIABLE s
varsPS == <<vars, p, s>>
INSTANCE Stuttering WITH vars <- varsP
TypeOKPS == TypeOKP /\ (s \in {top}  \cup 
                           [id: {"DoWr"}, 
                            ctxt : Writers,
                            val : SUBSET Readers] \cup 
                            [id: {"BeginRd"}, 
                            ctxt : Readers,
                            val : SUBSET Readers])
                            
InitPS == InitP /\ (s = top)

BeginRdPS(i)       == PostStutter(BeginRdP(i), "BeginRd", i, {}, {}, 
                                   LAMBDA j : j)
BeginWrPS(i, cmd)  == NoStutter(BeginWrP(i, cmd))
DoWrPS(i)          == PostStutter(DoWrP(i), "DoWr", i, {}, 
                                   {j \in Readers : 
                                     (rstate[j] # << >>) /\ (p[j] = Len(rstate'[j]))},
                                   LAMBDA S : S \ {CHOOSE x \in S : TRUE})
IEndRdPS(i, j)     == NoStutter(IEndRdP(i, j))
EndWrPS(i)         == NoStutter(EndWrP(i))

NextPS ==  \/ \E i \in Readers : \/ BeginRdPS(i)  
                                 \/ \E j \in 1..Len(rstate[i]) : IEndRdPS(i,j)
           \/ \E i \in Writers : \/ \E cmd \in RegVals : BeginWrPS(i, cmd)
                                 \/ DoWrPS(i) \/ EndWrPS(i)

SpecPS == InitPS /\ [][NextPS]_varsPS /\ Fairness
-----------------------------------------------------------------------------
istateBar == [i \in Readers \cup Writers |->
                IF i \in Writers 
                  THEN wstate[i]
                  ELSE IF rstate[i] = << >> 
                         THEN interface[i]
                         ELSE IF p[i] = 1 
                                THEN IF /\ s # top 
                                        /\ s.id  = "BeginRd"
                                        /\ s.ctxt = i
                                       THEN NotMemVal
                                       ELSE rstate[i][1]
                                ELSE IF \/ p[i] > Len(rstate[i])
                                        \/ /\ s # top
                                           /\ s.id = "DoWr"
                                           /\ i \in s.val
                                       THEN NotMemVal
                                       ELSE rstate[i][p[i]] ]    

LS == INSTANCE LinearSnapshot WITH istate <- istateBar                                       
=============================================================================
\* Modification History
\* Last modified Mon Oct 10 23:14:44 PDT 2016 by lamport
\* Created Wed Oct 05 02:26:43 PDT 2016 by lamport
