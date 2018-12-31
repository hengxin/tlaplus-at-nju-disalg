----------------------- MODULE SetUtils -----------------------
(***************************************************************************)
(* Copyright: https://www.learntla.com/libraries/sets/                     *)
(***************************************************************************)
EXTENDS TLC
LOCAL INSTANCE Naturals

(***************************************************************************)
(* Pick an element from the set S.                                         *)
(***************************************************************************)
Pick(S) == CHOOSE s \in S : TRUE
(***************************************************************************)
(* Pick an element that is not in the set S.                               *)
(***************************************************************************)
PickNone(S) == CHOOSE s : s \notin S

RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == 
    IF S = {} 
    THEN value 
    ELSE LET s == Pick(S) 
         IN  SetReduce(Op, S \ {s}, Op(s, value)) 
(***************************************************************************)
(* This version will report an error if                                    *)
(* the operation applied is not commutative as required.                   *)
(***************************************************************************)
RECURSIVE SetReduceSafe(_, _, _)
SetReduceSafe(Op(_, _), S, value) == 
    IF S = {} 
    THEN value
    ELSE LET s == Pick(S)
         IN  IF Op(s, value) = Op(value, s) 
             THEN SetReduceSafe(Op, S \ {s}, Op(s, value)) 
             ELSE Assert(FALSE, "Op is not commutative.") 

Sum(S) == 
    LET sum(a, b) == a + b
    IN  SetReduce(sum, S, 0)
    
IsMin(set,min) ==
    /\ min \in set
    /\ (\A x \in set:min \leq x)

IsMax(set,max) ==
    /\ max \in set
    /\ (\A x \in set:max \geq x)

MinOfSet(set) == CHOOSE min \in set:(\A x \in set: min \leq x)

MaxOfSet(set) == CHOOSE max \in set:(\A x \in set: max \geq x)
=============================================================================
\* Modification History
\* Last modified Tue Dec 04 19:43:16 CST 2018 by hengxin
\* Created Fri Jul 06 13:21:26 CST 2018 by hengxin