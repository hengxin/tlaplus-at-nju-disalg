--------------------------- MODULE SendSeqUndoP ----------------------------
(***************************************************************************)
(* This module adds a prophecy variable p to specification SpecU of module *)
(* SendSeqUndo to obtain the specification SpecUP.  It then asserts that   *)
(* SpecUP implements specification Spec of module SendSeq under a suitable *)
(* refinement mapping, which implies that SpecU implements \EE y : Spec.   *)
(***************************************************************************)
EXTENDS SendSeqUndo

(***************************************************************************)
(* Our definitions make use of the operators defined in module Prophecy.   *)
(* You should read that module to understand the meanings of those         *)
(* operators.  We begin by defining the set Pi of possible individual      *)
(* predictions and the domain Dom of p, where p[d] makes a prediction      *)
(* associated with d.  In this case, d is the domain of y (which equals    *)
(* 1..Len(y)), and p[d] predicts whether element number d of y is either   *)
(* sent or undone (removed from y by an Undo step).                        *)
(***************************************************************************)
Pi == {"send", "undo"}
Dom == DOMAIN y

INSTANCE Prophecy WITH Pi <- {"send", "undo"}, DomPrime <- Dom'

(***************************************************************************)
(* Adding the prophecy variable requires replacing each subaction `A' of a *)
(* disjunctive representation with an action Ap.  We use the disjunctive   *)
(* representation with subactions Choose, Send, Rcv, and Undo(i).  Each    *)
(* action Ap is defined by defining:                                       *)
(*                                                                         *)
(*  - An operator PredA, where PredA(p) is the prediction that the value   *)
(*    of p is making about action `A'.                                     *)
(*                                                                         *)
(*  - PredDomA, the subset of Dom consisting of the elements d for which   *)
(*    p[d] is used in the prediction PredA(p).                             *)
(*                                                                         *)
(*  - DomInjA, an injection from a subset of Dom to Dom' describing the    *)
(*    correspondence between predictions made by p and those made by p'.   *)
(*    For the prophecy variable we are defining, DomInjA specifies the     *)
(*    obvious correspondence between the elements of the sequences y and   *)
(*    y'.                                                                  *)
(*                                                                         *)
(* These definitions for each subaction `A' follow.  For example,          *)
(* PredDomChoose is PredDomA for `A' the Choose action.                    *)
(***************************************************************************)
PredDomChoose == {}
DomInjChoose  == [i \in Dom |-> i]
PredChoose(p) == TRUE

PredDomSend == {1}
DomInjSend  == [i \in 2..Len(y) |-> i-1]
PredSend(p) == p[1] = "send"

PredDomRcv == {}
DomInjRcv  == [d \in Dom |-> d]
PredRcv(p) == TRUE

PredDomUndo(i) == {i}
DomInjUndo(i)  == [j \in 1..Len(y) \ {i} |-> IF j < i THEN j ELSE j-1]
PredUndo(p, i) == p[i] = "undo"

(***************************************************************************)
(* The following theorem asserts the action requirements described in      *)
(* Section 4.5 of "Auxiliary Variables in TLA+", which must be satisfied   *)
(* to ensure that \EE p : SpecUP is equivalent to SpecU.                   *)
(***************************************************************************)
Condition  == /\ ProphCondition(Choose, DomInjChoose, PredDomChoose, 
                                PredChoose)
              /\ ProphCondition(Send, DomInjSend, PredDomSend, PredSend)
              /\ ProphCondition(Rcv, DomInjRcv, PredDomRcv, PredRcv)
              /\ \A i \in Dom : 
                    ProphCondition(Undo(i), DomInjUndo(i), PredDomUndo(i),  
                                   LAMBDA p : PredUndo(p, i))

THEOREM SpecU => [][Condition]_vars    
(***************************************************************************)
(* Temporarily end the module here to use TLC to check the theorem.        *)
(***************************************************************************)
----------------------------------------------------------------------------
VARIABLE p
varsP == <<vars, p>>

TypeOKP == TypeOK /\ (p \in [Dom -> Pi])

InitUP == Init /\ (p \in [Dom -> Pi])

(***************************************************************************)
(* The actions Ap are defined using the ProphAction operator defined in    *)
(* the Prophecy module.                                                    *)
(***************************************************************************)
ChooseP == ProphAction(Choose, p, p', 
                        DomInjChoose, PredDomChoose, PredChoose)

SendP == ProphAction(Send, p, p', DomInjSend, PredDomSend, PredSend)

          
RcvP == ProphAction(Rcv, p, p', DomInjRcv, PredDomRcv, PredRcv)

UndoP(i) == ProphAction(Undo(i), p, p', DomInjUndo(i), PredDomUndo(i), 
                        LAMBDA j : PredUndo(j, i))

NextUP == ChooseP \/ SendP \/ RcvP \/ (\E i \in 1..Len(y) : UndoP(i))

SpecUP == InitUP /\ [][NextUP]_varsP
----------------------------------------------------------------------------
(***************************************************************************)
(* The theorem below asserts that SpecUP implements specification Spec of  *)
(* module SendSeq under the refinement mapping y <- yBar, where yBar is    *)
(* defined here to be the subsequence of y consisting of those elements    *)
(* for which p predicts "send".                                            *)
(***************************************************************************)
yBar ==  LET RECURSIVE R(_, _)
             R(yseq, pseq) ==
                IF yseq = << >> 
                  THEN yseq
                  ELSE IF Head(pseq) = "send" 
                         THEN <<Head(yseq)>> \o R(Tail(yseq), Tail(pseq))
                         ELSE  R(Tail(yseq), Tail(pseq))
         IN  R(y, p)        

SS == INSTANCE SendSeq WITH y <- yBar

THEOREM SpecUP => SS!Spec 
=============================================================================
\* Modification History
\* Last modified Sat Dec 31 16:10:30 PST 2016 by lamport
\* Created Thu Sep 15 02:52:00 PDT 2016 by lamport
