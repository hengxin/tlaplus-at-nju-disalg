------------------------------ MODULE MinMax2 -------------------------------
(***************************************************************************)
(* This module specifies a system with the same interaction between a user *)
(* and a server as the one in module MinMax1, but instead of remembering   *)
(* the entire set of inputs, it uses two variables min and max to keep the *)
(* largest and smallest values input thus far.  Initially min equals       *)
(* Infinity and max equals MinusInfinity, where Infinity and MinusInfinity *)
(* are two values that are considered greater than and less than any       *)
(* integer, respectively.                                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS Lo, Hi, Both, None
ASSUME {Lo, Hi, Both, None} \cap Int = { }

Infinity      == CHOOSE n : n \notin Int
MinusInfinity == CHOOSE n : n \notin (Int \cup {Infinity})

(***************************************************************************)
(* The operators IsLeq and IsGeq extend =< and >=, respectively, to have   *)
(* the correct meaning when Infinity or MinusInfinity is one of the        *)
(* arguments.                                                              *)
(***************************************************************************)
IsLeq(i, j) == (j = Infinity) \/ (i =< j)
IsGeq(i, j) == (j = MinusInfinity) \/ (i >= j) 

(***************************************************************************)
(* The rest of the specification is straightforward.                       *)
(***************************************************************************)
VARIABLES x, turn, min, max
vars == <<x, turn, min, max>>

Init ==  /\ x = None
         /\ turn = "input" 
         /\ min = Infinity 
         /\ max = MinusInfinity

InputNum ==  /\ turn = "input"
             /\ turn' = "output"
             /\ x' \in Int
             /\ UNCHANGED <<min, max>>

Respond  ==  /\ turn = "output"
             /\ turn' = "input"
             /\ min' = IF IsLeq(x, min) THEN x ELSE min 
             /\ max' = IF IsGeq(x, max) THEN x ELSE max
             /\ x' = IF x = max' THEN IF x = min' THEN Both ELSE Hi  
                                 ELSE IF x = min' THEN Lo   ELSE None
          
Next == InputNum \/ Respond

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Fri Oct 21 23:57:32 PDT 2016 by lamport
\* Created Fri Aug 26 14:32:23 PDT 2016 by lamport
