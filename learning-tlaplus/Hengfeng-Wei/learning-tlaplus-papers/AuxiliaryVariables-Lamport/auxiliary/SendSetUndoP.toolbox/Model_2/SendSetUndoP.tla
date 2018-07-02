--------------------------- MODULE SendSetUndoP ----------------------------
(***************************************************************************)
(* This module is part of the example in Section 4.4 of the paper          *)
(* "Auxiliary Variables in TLA+".  It defines the specification SpecUP     *)
(* obtained, as explained in that paper, by adding a prophecy-array        *)
(* variable p to specification SpecU of module SendSetUndo.  It then       *)
(* defines a refinement mapping under which SpecUP implements              *)
(* specification Spec of module SendSet to show that SpecUP implements     *)
(* \EE y : Spec.                                                           *)
(***************************************************************************)
EXTENDS SendSetUndo

(***************************************************************************)
(* The value of the variable p is always a function with domain y, which   *)
(* we call Dom to conform to the notation of Section 4.4 of "Auxiliary     *)
(* Variables in TLA+".  The value of p[d] predicts whether the element d   *)
(* of y will be sent or simply undone--that is, removed from y by an       *)
(* Undo(S) action.  These two predictions are represented by the string    *)
(* values "send" and "undo".                                               *)
(***************************************************************************)
Pi  == {"send", "undo"}
Dom == y

(***************************************************************************)
(* As explained in the paper, the SpecUP is obtained by replacing each     *)
(* subaction A of SpecU with the subaction                                 *)
(*                                                                         *)
(*    Ap == A /\ PredA(p) /\ (p' \in NewPSetA(p))                          *)
(*                                                                         *)
(* For the reason explained below, we define PredA and NewPSetA before the *)
(* variable p is declared, so we must define them to be operators that     *)
(* take p as an argument in the definition of Ap.                          *)
(*                                                                         *)
(* The definitions of PredA and NewPSetA are given below, for the four     *)
(* subactions A in the obvious disjunctive representation of NextU.  (For  *)
(* example, PredChoose is PredA for A equal to Choose.)                    *)
(***************************************************************************)
PredChoose(p)    == TRUE
NewPSetChoose(p) == {f \in [Dom' -> Pi]  :  \A d \in Dom : f[d] = p[d]}

PredSend(p)    == p[x'] = "send"
NewPSetSend(p) == { [d \in Dom' |-> p[d]] }

PredRcv(p)    == TRUE
NewPSetRcv(p) == {p}

PredUndo(p, S) == \A d \in S : p[d] = "undo"
NewPSetUndo(p) == { [d \in Dom' |-> p[d]] }

(***************************************************************************)
(* The following theorem must hold for p to be an auxiliary variable--that *)
(* is, for \EE p : SpecUP to be equivalent to SpecU.  It is equivalent to  *)
(* the conjunction of (4.11) of "Auxiliary Variables in TLA+" for the four *)
(* subactions A.  Note that we need each PredA to be an operator in order  *)
(* to state this condition.  We make NewPSetA an operator as well so we    *)
(* can put the two definitions together.                                   *)
(*                                                                         *)
(* To check this theorem with TLA+, the module must be temporarily ended   *)
(* after the theorem so a model can be created having SpecU as its         *)
(* specification.                                                          *)
(***************************************************************************)
Condition == [][/\ Choose => \E f \in [Dom -> Pi] : PredChoose(f)
                /\ Send   => \E f \in [Dom -> Pi] : PredSend(f)
                /\ Rcv    => \E f \in [Dom -> Pi] : PredRcv(f)
                /\ \A S \in (SUBSET y) \ {{}}  : 
                       Undo(S) => \E f \in [Dom -> Pi] : PredUndo(f,S)
               ]_vars
               
THEOREM SpecU => Condition
------------------------------------------------------------------------------
VARIABLE p
varsP == <<vars, p>>

TypeOKP == TypeOK /\ (p \in [Dom -> Pi])

(***************************************************************************)
(* Since Dom equals y, which initially equals the empty set, the initial   *)
(* value of p is the unique function with empty domain.                    *)
(***************************************************************************)
InitUP == Init /\ (p = << >>)

(***************************************************************************)
(* The rest of the specification is as explained above.                    *)
(***************************************************************************)
ChooseP  == Choose  /\ PredChoose(p)  /\ (p' \in NewPSetChoose(p))
SendP    == Send    /\ PredSend(p)    /\ (p' \in NewPSetSend(p))
RcvP     == Rcv     /\ PredRcv(p)     /\ (p' \in NewPSetRcv(p))
UndoP(S) == Undo(S) /\ PredUndo(p, S) /\ (p' \in NewPSetUndo(p))

NextUP == ChooseP \/ SendP \/ RcvP \/ (\E S \in (SUBSET y) \ {{}} : UndoP(S))

SpecUP == InitUP /\ [][NextUP]_varsP
-----------------------------------------------------------------------------
(***************************************************************************)
(* The INSTANCE statement and theorem assert that SpecUP implements        *)
(* specification Spec of module SendSet under the indicated refinement     *)
(* mapping.                                                                *)
(***************************************************************************)
SS == INSTANCE SendSet WITH y <- {d \in y : p[d] = "send"}
THEOREM SpecUP => SS!Spec
=============================================================================
\* Modification History
\* Last modified Sat Oct 22 00:47:46 PDT 2016 by lamport
\* Created Sun Sep 25 05:58:07 PDT 2016 by lamport
