--------------------------------- MODULE Op ---------------------------------
(*********************************************************************)
(* Model checking basic operations on strings                        *)
(* (i.e., list of characters).                                       *)
(*********************************************************************)
EXTENDS Naturals, Sequences, 
    AdditionalMathOperators, AdditionalSetOperators, AdditionalSequenceOperators
----------------------------------------------------------------------
CONSTANTS   Char   \* set of characters allowed

List == Seq(Char)   \* all possible lists/strings
----------------------------------------------------------------------
(*********************************************************************)
(* The set of all operations.                                        *)
(*********************************************************************)
Rd == [type: {"Rd"}] \* a read specifies no arguments
Ins == [type: {"Del"}, pos: 1 .. PosInt] \* a deletion specifies a position, indexed from 1
Del == [type: {"Ins"}, pos: 1 .. PosInt, ch: Char, pr: 1 .. PosInt] \* an insertion also specifies a character and a priority

Op == Ins \cup Del  \* Now we focus on "Ins" and "Del".
      
Nop == PickNone(Op)  \* Nop: an operation representing "doing nothing"
-----------------------------------------------------------------------------
(*********************************************************************)
(* Some operations for test.                                         *)
(*********************************************************************)
Del1 == [type |-> "Del", pos |-> 1]
Del2 == [type |-> "Del", pos |-> 2]
Del3 == [type |-> "Del", pos |-> 3]
Del4 == [type |-> "Del", pos |-> 4]
Ins1 == [type |-> "Ins", pos |-> 1, ch |-> "a", pr |-> 1]
Ins2 == [type |-> "Ins", pos |-> 2, ch |-> "b", pr |-> 2]
Ins3 == [type |-> "Ins", pos |-> 3, ch |-> "c", pr |-> 3]
Ops == <<Ins2, Del3, Ins1, Del2, Ins3, Del1>>
-----------------------------------------------------------------------------
(*********************************************************************)
(* The "Apply" operator which applies an operation op on the list l. *)
(* Del: If pos > Len(l), the last element of l is deleted.           *)
(*      This is realized by the DeleteElement operator.              *)
(* Ins: If pos > Len(l), the new element is appended to l.           *)
(*      This is realized by the InsertElement operator.              *)
(*********************************************************************)
Apply(op, l) == CASE op = Nop -> l 
                 []  op.type = "Del" -> DeleteElement(l, op.pos)
                 []  op.type = "Ins" -> InsertElement(l, op.ch, op.pos)

(*********************************************************************)
(* The "ApplyOps" operator which applies an operation sequence ops   *)
(* on the list l.                                                    *)
(*********************************************************************)
RECURSIVE ApplyOps(_, _)
ApplyOps(ops, l) ==
    IF ops = <<>>
    THEN l
    ELSE Apply(Last(ops), ApplyOps(AllButLast(ops), l))
=============================================================================
\* Modification History
\* Last modified Sat Jul 07 10:59:03 CST 2018 by hengxin
\* Created Sat Jun 23 20:56:53 CST 2018 by hengxin