--------------------------------- MODULE Op ---------------------------------
(*********************************************************************)
(* Model checking basic operations on strings                        *)
(* (i.e., list of characters).                                       *)
(*********************************************************************)
EXTENDS Naturals, Sequences, AdditionalSequenceOperators
----------------------------------------------------------------------
CONSTANTS   Char,
            MaxPos,
            MaxPr,
            MaxLen
            
ASSUME /\ MaxPos \in Nat \ {0}  \* WARNING: index from 1
       /\ MaxPr \in Nat \ {0}
       /\ MaxLen \in Nat \ {0}
----------------------------------------------------------------------
\* List == Seq(Char)   \* The set of all lists.
List == UNION {[1 .. m -> Char] : m \in 0 .. MaxLen}

(*********************************************************************)
(* The set of all operations.                                        *)
(* In this specification, we will focus on "Ins" and "Del".          *)
(*********************************************************************)
Op == \* [type: {"Rd"}] \cup \* a read specifies no arguments
      [type: {"Del"}, pos: 1 .. MaxPos] \cup \* a deletion specifies a position 
      [type: {"Ins"}, pos: 1 .. MaxPos, ch: Char, pr: 1 .. MaxPr] \* an insertion specifies a position, a character, and a priority

Nop == CHOOSE v : v \notin Op  \* Nop: an operation representing "doing nothing"
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
(*********************************************************************)
Apply(op, l) == 
    LET len == Len(l) 
        pos == op.pos
    IN CASE op = Nop -> l
        []  op.type = "Del" -> SubSeq(l, 1, pos - 1) \o SubSeq(l, pos + 1, len) 
        []  op.type = "Ins" -> Append(SubSeq(l, 1, pos - 1), op.ch) \o SubSeq(l, pos, len)

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
\* Last modified Tue Jul 03 16:03:00 CST 2018 by hengxin
\* Created Sat Jun 23 20:56:53 CST 2018 by hengxin