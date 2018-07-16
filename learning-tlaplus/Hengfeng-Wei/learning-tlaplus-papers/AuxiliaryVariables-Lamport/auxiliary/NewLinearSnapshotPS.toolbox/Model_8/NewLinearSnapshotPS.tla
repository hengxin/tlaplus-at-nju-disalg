------------------------ MODULE NewLinearSnapshotPS ------------------------
(***************************************************************************)
(* This module adds a prophecy variable and then a stuttering variable to  *)
(* specification Spec of module NewLinearSnapshot.  It then shows that the *)
(* resulting spec SpecPS implements the linearizable specification `Spec'  *)
(* of module LinearSnapshot.  This shows that if Spec_NL is specification  *)
(* `Spec' of NewLinearSnaphot and Spec_L is specification Spec of          *)
(* LinearSnapshot, then \EE mem, rstate, wstate : Spec_NL implies \EE mem, *)
(* istate : Spec_L.                                                        *)
(***************************************************************************)
EXTENDS NewLinearSnapshot

(***************************************************************************)
(* We first add the prophecy variable p so that, whenever a reader i is    *)
(* executing a read operation, p[i] predicts the value j such that the     *)
(* EndRd(i) action will produce rstate[i][j] as its output.                *)
(*                                                                         *)
(* Our definitions make use of the operators defined in module Prophecy.   *)
(* You should read that module to understand the meanings of those         *)
(* operators.  We begin by defining the set Pi of possible predictions and *)
(* the domain Dom of p.                                                    *)
(***************************************************************************)
Pi == Nat \ {0}
Dom == {r \in Readers : rstate[r] # << >>}
INSTANCE Prophecy WITH DomPrime <- Dom'

(***************************************************************************)
(* To add the prophecy variable, it's convenient to use a different        *)
(* disjunctive representation of the next-state action Next of Spec than   *)
(* we used in writing its definition.  Instead of having EndRd(i) as a     *)
(* subaction, we want to write it as an existential quantification over    *)
(* the action IEndRd(i, j), which is an EndRd(i) action that returns       *)
(* rstate[i][j] as its output.  We now define IEndRd and define Nxt to the *)
(* the next-state action Next rewritten in terms of IEndRd.  Of course,    *)
(* Nxt should be equivalent to Next.                                       *)
(***************************************************************************)
IEndRd(i, j) == /\ interface[i] = NotMemVal
                /\ interface' = [interface EXCEPT ![i] = rstate[i][j]]
                /\ rstate' = [rstate EXCEPT ![i] = << >>]
                /\ UNCHANGED <<mem, wstate>>

Nxt == \/ \E i \in Readers : \/ BeginRd(i)  
                             \/ \E j \in 1..Len(rstate[i]) : IEndRd(i,j)
       \/ \E i \in Writers : \/ \E cmd \in RegVals : BeginWr(i, cmd)
                             \/ DoWr(i) \/ EndWr(i)

(***************************************************************************)
(* We should check that we haven't made a mistake, and that Nxt is indeed  *)
(* equivalent to Next.  We could use TLC to check this.  However, the      *)
(* equivalence is so obvious that the TLAPS proof system can check it      *)
(* easily by just expanding the appropriate definitions.  So, we let TLAPS *)
(* do the checking of the following theorem.                               *)
(***************************************************************************)
THEOREM Next <=> Nxt
BY DEF Next, Nxt, EndRd, IEndRd

(***************************************************************************)
(* Adding the prophecy variable requires replacing each subaction `A' of   *)
(* the disjunctive representation implied by the definition of Nxt with an *)
(* action Ap.  Each action Ap is defined by defining:                      *)
(*                                                                         *)
(*  - An operator PredA, where PredA(p) is the prediction that the value   *)
(*    of p is making about action `A'.                                     *)
(*                                                                         *)
(*  - PredDomA, the subset of Dom consisting of the elements d for which   *)
(*    p[d] is used in the prediction PredA(p).                             *)
(*                                                                         *)
(*  - DomInjA, an injection from a subset of Dom to Dom' describing the    *)
(*    correspondence between predictions made by p and those made by p'.   *)
(*    For the prophecy variable we are defining, DomInjA is the identity   *)
(*    function on Dom \cap Dom'.  The Prophecy module defines IdFcn(S)     *)
(*    to be the identity function on the set S.                            *)
(*                                                                         *)
(* These definitions for each subaction `A' follow.  For example,          *)
(* PredBeginRd is PredA for `A' the BeginRd(i) action.                     *)
(***************************************************************************)
PredBeginRd(p) == TRUE
PredDomBeginRd == {}
DomInjBeginRd  == IdFcn(Dom)

(***************************************************************************)
(* For the IEndRd(p, i, j) action, the PredA operator depends on the       *)
(* values of the two bound identifiers in the action's context (named i    *)
(* and j in the definition of Nxt).                                        *)
(***************************************************************************)
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

(***************************************************************************)
(* We next define the formula Condition, where the property                *)
(*                                                                         *)
(*    Spec => Condition                                                    *)
(*                                                                         *)
(* must hold for the specification SpecP defined below be obtained from    *)
(* `Spec' by adding an auxiliary variable--that is, for SpecP to satisfy:  *)
(*                                                                         *)
(*    (\EE p : SpecP)  <=>  Spec                                           *)
(*                                                                         *)
(* Note how the LAMBDA expression is used to "convert" PredIEndRd to the   *)
(* single-argument operator with the appropriate meaning required as an    *)
(* argument to ProphCondition.                                             *)
(***************************************************************************)
Condition ==
 [][ /\ \A i \in Readers :
          /\ ProphCondition(BeginRd(i), DomInjBeginRd, 
                            PredDomBeginRd, PredBeginRd)
          /\ \A j \in 1..Len(rstate[i]) :
                ProphCondition(IEndRd(i, j), DomInjIEndRd, 
                               PredDomIEndRd(i),
                               LAMBDA p : PredIEndRd(p, i, j))
     /\ \A i \in Writers :
          /\ \A cmd \in RegVals :
                ProphCondition(BeginWr(i, cmd), DomInjBeginWr, 
                               PredDomBeginWr, PredBeginWr)
          /\ ProphCondition(DoWr(i), DomInjDoWr, PredDomDoWr, 
                            PredDoWr)
          /\ ProphCondition(EndWr(i), DomInjEndWr, PredDomEndWr, 
                            PredEndWr)
   ]_vars

(***************************************************************************)
(* You can have TLC check the property Spec => Condition by temporarily    *)
(* ending the module here and creating a model with Spec as the            *)
(* specification and Condition as a property to be checked.                *)
(***************************************************************************)

(***************************************************************************)
(* We now declare the variable p and define SpecP using the ProphAction    *)
(* operator defined in the Prophecy module.  That operator defines         *)
(*                                                                         *)
(*     ProphAction(A, p, p', DomInjA, PredDomA, PredA)                     *)
(*                                                                         *)
(* to be the action Ap that replaces the subaction `A'.  The general form  *)
(* of the initial predicate is Init /\ (p \in [Dom -> Pi]).  Since Init    *)
(* implies that Dom is the empty set, [Dom -> Pi] is just {EmptyFcn},      *)
(* where EmptyFcn is defined in the Prophecy module to equal the function  *)
(* with empty domain, and p \in {EmptyFcn} of course is equivalent to p =  *)
(* EmptyFcn.                                                               *)
(*                                                                         *)
(* Note how SpecP is the conjunction of InitP /\ [][NextP]_varsP and the   *)
(* liveness property of Spec.                                              *)
(***************************************************************************)
VARIABLE p
varsP == <<vars, p>>

TypeOKP == TypeOK /\ (p \in [Dom -> Pi])

InitP == Init /\ (p = EmptyFcn)

BeginRdP(i) == ProphAction(BeginRd(i), p, p', DomInjBeginRd,  
                           PredDomBeginRd, PredBeginRd)

BeginWrP(i, cmd) == ProphAction(BeginWr(i, cmd), p, p', DomInjBeginWr,  
                                PredDomBeginWr, PredBeginWr)
          
DoWrP(i) == ProphAction(DoWr(i), p, p', DomInjDoWr, PredDomDoWr, 
                        PredDoWr)

IEndRdP(i, j) == 
   ProphAction(IEndRd(i, j),  p, p', DomInjIEndRd, 
               PredDomIEndRd(i), LAMBDA q : PredIEndRd(q, i, j))

EndWrP(i) == ProphAction(EndWr(i), p, p', DomInjEndWr, PredDomEndWr, 
                         PredEndWr)

NextP == \/ \E i \in Readers : \/ BeginRdP(i)  
                               \/ \E j \in 1..Len(rstate[i]) : IEndRdP(i,j)
         \/ \E i \in Writers : \/ \E cmd \in RegVals : BeginWrP(i, cmd)
                               \/ DoWrP(i) \/ EndWrP(i)

SpecP == InitP /\ [][NextP]_varsP /\ Fairness
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define SpecPS by adding to SpecP a stuttering variable s that    *)
(* adds:                                                                   *)
(*                                                                         *)
(*   - A single stuttering step immediately after a BeginRdP(i) step if    *)
(*     p[i] predicts that EndRdP(i) will produce as output rstate[1].      *)
(*                                                                         *)
(*   - Stuttering steps immediately after DoWrP(i), one such step for      *)
(*     every reader j for which p[j] predicts that the EndRdP(j) step      *)
(*     will produce as output the value of mem immediately after the       *)
(*     DoWrP(i) step.                                                      *)
(*                                                                         *)
(* Each of these stuttering steps will become a DoRd step of               *)
(* LinearSnapshot under our refinement mapping.                            *)
(*                                                                         *)
(* A stuttering variable s is added by replacing each subaction `A' of a   *)
(* disjunctive decomposition of the next-state action by an action `As'.   *)
(* Action `As' adds stuttering steps to `A' by setting the component s.val *)
(* to an initial value InitVal and having each stuttering step replace     *)
(* s.val by decr(s.val) for a "decrementing" operator decr, until s.val    *)
(* has the value `bot'.  To add a single stuttering step to BeginRd(i), we *)
(* let InitVal = 1, `bot' = 0, and decr(x) = x-1.  To add a stuttering     *)
(* step after DoWr(i) for each reader in a set R of readers, we let        *)
(* InitVal = R, `bot' = {}, and decr(x) equal a set obtained by removing a *)
(* single element from the set x.                                          *)
(*                                                                         *)
(* The correctness condition for adding stuttering steps to an action `A'  *)
(* is that there is some set `Sigma' such that (1) InitVal \in `Sigma',    *)
(* (2) `bot' \in `Sigma', and (3) for any sig \in `Sigma', repeatedly      *)
(* decrementing sig with decr eventually reaches `bot'.  For BeginRd(i) we *)
(* let `Sigma' equal {0,1}; for DoWr(i) we let `Sigma' equal the set       *)
(* SUBSET Readers of all subsets of the set Readers.  The two theorems     *)
(* below express condition (1) for these two subactions.  They are         *)
(* trivially true because the following two formulas are trivially true:   *)
(*                                                                         *)
(*    (IF ... THEN 1 ELSE 0) \in {0, 1}                                    *)
(*                                                                         *)
(*    {j \in Readers : ...} \in (SUBSET Readers)                           *)
(***************************************************************************)
THEOREM SpecP => [][\A i \in Readers : BeginRdP(i) =>
                      (IF p'[i] = 1 THEN 1 ELSE 0) \in {0,1}]_varsP

THEOREM SpecP => [][\A i \in Writers, cmd \in RegVals :
                      DoWrP(i) =>
                        {j \in Readers : (rstate[j] # << >>)
                                            /\  (p[j] = Len(rstate'[j]))}
                          \in (SUBSET Readers)]_varsP
(***************************************************************************)
(* Temporarily end the module here to have TLC test the correctness of the *)
(* preceding two theorems.                                                 *)
(***************************************************************************)

(***************************************************************************)
(* We now declare the variable s and define the initial predicate InitPS   *)
(* and next-state action NextPS of SpecPS.  When stuttering steps are not  *)
(* being taken, s equals `top', a value defined in module Stuttering.      *)
(* When stuttering steps are being taken, s equals a record with           *)
(* components:                                                             *)
(*                                                                         *)
(*    s.val: Described above.                                              *)
(*                                                                         *)
(*    s.id: A value that identifies the action to which stutterin steps    *)
(*          are being added.                                               *)
(*                                                                         *)
(*    s.ctxt: The value of bound identifiers in the context of the action  *)
(*            for which the action is being executed.                      *)
(***************************************************************************)
VARIABLE s
varsPS == <<vars, p, s>>

INSTANCE Stuttering WITH vars <- varsP 

TypeOKPS == TypeOKP /\ (s \in {top}  \cup 
                           [id: {"DoWr"}, 
                            ctxt : Writers,
                            val : SUBSET Readers] \cup 
                            [id: {"BeginRd"}, 
                            ctxt : Readers,
                            val : {0,1}]) 
                            
InitPS == InitP /\ (s = top)

(***************************************************************************)
(* The actions `As' for each action `A' are defined using operators        *)
(* defined in the Stuttering module.  The assumptions assert correctness   *)
(* conditions (2) and (3), described in a comment above, for the two       *)
(* actions to which stuttering steps are added.                            *)
(***************************************************************************)
BeginRdPS(i) == MayPostStutter(BeginRdP(i), "BeginRd", i, 0, 
                               IF p'[i] = 1 THEN 1 ELSE 0, 
                               LAMBDA j : j-1)   

ASSUME StutterConstantCondition({0,1}, 0, LAMBDA j : j-1)    


BeginWrPS(i, cmd) == NoStutter(BeginWrP(i, cmd))

DoWrPS(i) == MayPostStutter(DoWrP(i), "DoWr", i, {}, 
                            {j \in Readers : 
                              (rstate[j] # << >>) /\ (p[j] = Len(rstate'[j]))},
                            LAMBDA S : S \ {CHOOSE x \in S : TRUE})

ASSUME StutterConstantCondition(SUBSET Readers, {}, 
                                LAMBDA S : S \ {CHOOSE x \in S : TRUE})                                
                      
IEndRdPS(i, j) == NoStutter(IEndRdP(i, j))

EndWrPS(i) == NoStutter(EndWrP(i))

NextPS == \/ \E i \in Readers : \/ BeginRdPS(i)  
                                \/ \E j \in 1..Len(rstate[i]) : IEndRdPS(i,j)
          \/ \E i \in Writers : \/ \E cmd \in RegVals : BeginWrPS(i, cmd)
                                \/ DoWrPS(i) \/ EndWrPS(i)

(***************************************************************************)
(* For convenience, we give a name to the safety part of the specification *)
(* as well as to the spec with its liveness condition.                     *)
(***************************************************************************)
SafeSpecPS == InitPS /\ [][NextPS]_varsPS
SpecPS == SafeSpecPS /\ Fairness
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the refinement mapping.  The externally visible variable  *)
(* `interface' is of course instantiated with the variable of the same     *)
(* name, as is the internal variable mem.  The internal variable istate is *)
(* instantiated by istateBar, defined here.  The value of istateBar, like  *)
(* the value of istate in spec Spec of module LinearSnapshot, is a         *)
(* function with domain Procs, which we have defined in this moduule to    *)
(* equal Readers \cup Writers.  For i \in Writers, we let istateBar[i]     *)
(* equal wstate[i].  The value of istate[i] for i \in Readers is more      *)
(* complicated.  It has to be defined so that the stuttering steps we      *)
(* added become the appropriate DoRd(i) steps under the refinement         *)
(* mapping.  You should study the definition to understand why they they   *)
(* are.                                                                    *)
(***************************************************************************)
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

(***************************************************************************)
(* The following INSTANCE statement and theorems assert that SafeSpecPS    *)
(* and SpecPS implement formulas SafeSpec and Spec, respectively, of       *)
(* module LinearSnapshot, under the refinement mapping.                    *)
(***************************************************************************)
LS == INSTANCE LinearSnapshot WITH istate <- istateBar  

THEOREM SafeSpecPS => LS!SafeSpec
THEOREM SpecPS => LS!Spec                                     
=============================================================================
\* Modification History
\* Last modified Sat Oct 22 01:50:44 PDT 2016 by lamport
\* Created Wed Oct 05 02:26:43 PDT 2016 by lamport
