------------------------------- MODULE MinMax1 ------------------------------
(***************************************************************************)
(* This module and modules MinMax2 and MinMax2H are used as examples in    *)
(* Sections 1 and 2 of the paper "Auxiliary Variables in TLA+".            *)
(*                                                                         *)
(* This module specifies a tiny system in which a user presents a server   *)
(* with a sequence of integer inputs, and the server responds to each      *)
(* input value i with with one of the following outputs: Hi if i is the    *)
(* largest number input so far, Lo if it's the smallest number input so    *)
(* far, Both if it's both, and None if it's neither.                       *)
(*                                                                         *)
(* The module is part of an example illustrating the use of a history      *)
(* variable.  The example includes this module, module MinMax2, and module *)
(* MinMax2H which adds a history variable to the specification of MinMax2  *)
(* and shows that the resulting specification implements implements the    *)
(* specification of the current module under a suitable refinement         *)
(* mapping.                                                                *)
(***************************************************************************)
EXTENDS Integers

(***************************************************************************)
(* We define setMax(S) and setMin(S) to be largest and smallest value in a *)
(* nonempty finite set S of integers.                                      *)
(***************************************************************************)
setMax(S) == CHOOSE t \in S : \A s \in S : t >= s
setMin(S) == CHOOSE t \in S : \A s \in S : t =< s

(***************************************************************************)
(* The possible values that can be returned by the system are declared to  *)
(* be constants, which we assume are not integers.                         *)
(***************************************************************************)
CONSTANTS Lo, Hi, Both, None
ASSUME {Lo, Hi, Both, None} \cap Int = { }

(***************************************************************************)
(* The the value of the variable x is the value input by the user or the   *)
(* value output by the system, the variable `turn' indicating which.  The  *)
(* variable y holds the set of all values input thus far.  We consider x   *)
(* and `turn' to be externally visible and y to be internal.               *)
(***************************************************************************)
VARIABLES x, turn, y
vars == <<x, turn, y>>

(***************************************************************************)
(* The initial predicate Init:                                             *)
(***************************************************************************)
Init ==  /\ x = None 
         /\ turn = "input" 
         /\ y = {}

(***************************************************************************)
(* The user's input action:                                                *)
(***************************************************************************)
InputNum ==  /\ turn = "input"
             /\ turn' = "output"
             /\ x' \in Int
             /\ y' = y

(***************************************************************************)
(* The systems response action:                                            *)
(***************************************************************************)
Respond == /\ turn = "output"
           /\ turn' = "input"
           /\ y' = y \cup {x}
           /\ x' = IF x = setMax(y') THEN IF x = setMin(y') THEN Both ELSE Hi  
                                     ELSE IF x = setMin(y') THEN Lo   ELSE None

(***************************************************************************)
(* The next-state action:                                                  *)
(***************************************************************************)  
Next == InputNum \/ Respond

(***************************************************************************)
(* The specification, which is a safety property (it asserts no liveness   *)
(* condition).                                                             *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariant to check (added by hengxin)                                   *)
(***************************************************************************)
NoneCertificate == [][/\ x \in Int 
                      /\ x < setMax(y \cup {x}) 
                      /\ x > setMin(y \cup {x})
                     <=> x' = None]_vars
-----------------------------------------------------------------------------
(***************************************************************************)
(* Below, we check that specification Spec implements specification Spec   *)
(* of module MinMax2 under a suitable refinement mapping.  The following   *)
(* definitions of Infinity and MinusInfinity are copied from module        *)
(* MinMax2.                                                                *)
(***************************************************************************)
Infinity      == CHOOSE n : n \notin Int
MinusInfinity == CHOOSE n : n \notin (Int \cup {Infinity})

M == INSTANCE MinMax2 
        WITH min <- IF y = {} THEN Infinity      ELSE setMin(y),
             max <- IF y = {} THEN MinusInfinity ELSE setMax(y)

(***************************************************************************)
(* The following theorem asserts that Spec implements the specification    *)
(* Spec of module MinMax2 under the refinement mapping defined by the      *)
(* INSTANCE statement.  The theorem can be checked with TLC using a model  *)
(* having M!Spec as the temporal property to be checked.                   *)
(***************************************************************************)
THEOREM Spec => M!Spec
=============================================================================
\* Modification History
\* Last modified Tue Jun 26 17:51:08 CST 2018 by hengxin
\* Last modified Tue Jun 26 17:29:03 CST 2018 by hengxin
\* Last modified Fri Oct 21 23:48:10 PDT 2016 by lamport
\* Created Fri Aug 26 14:28:26 PDT 2016 by lamport
