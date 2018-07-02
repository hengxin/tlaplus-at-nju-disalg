------------------------------ MODULE MinMax2H -----------------------------
(***************************************************************************)
(* This module defines SpecH to be a specification obtained by adding a    *)
(* history variable h to the specification Spec of module MinMax2.  It     *)
(* then shows that SpecH implements specification Spec of module MinMax1   *)
(* under the refinment mapping y <- h.                                     *)
(***************************************************************************)
EXTENDS MinMax2

VARIABLE h
varsH == <<vars, h>>

(***************************************************************************)
(* InitH is the initial predicate of SpecH and NextH is its next-state     *)
(* action, obtained by adding the history variable h to the subactions     *)
(* InputNum and Respond of the obvious disjunctive representation of Next. *)
(* (Disjunctive representations are explained in Section 3.2 of the paper  *)
(* "Auxiliary Variables in TLA+".)                                         *)
(***************************************************************************)
InitH == Init /\ (h = {})

InputNumH ==  /\ InputNum
              /\ h' = h

RespondH == /\ Respond
            /\ h' = h \cup {x}
          
NextH == InputNumH \/ RespondH

SpecH == InitH /\ [][NextH]_varsH
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following statement and theorem assert that SpecH implements        *)
(* specification Spec of module MinMax1 under the refinement mapping y <-  *)
(* h.                                                                      *)
(***************************************************************************)
M == INSTANCE MinMax1 WITH y <- h 

THEOREM SpecH => M!Spec
=============================================================================
\* Modification History
\* Last modified Fri Oct 21 23:59:25 PDT 2016 by lamport
\* Created Fri Aug 26 14:51:37 PDT 2016 by lamport
