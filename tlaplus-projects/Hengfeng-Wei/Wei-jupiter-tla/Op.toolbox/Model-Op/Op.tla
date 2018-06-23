--------------------------------- MODULE Op ---------------------------------
(*********************************************************************)
(* Model checking basic operations on strings                        *)
(* (i.e., list of characters).                                       *)
(*********************************************************************)
EXTENDS Naturals, Sequences
----------------------------------------------------------------------
CONSTANTS   Char
----------------------------------------------------------------------
List == Seq(Char)   \* The set of all lists.
(*********************************************************************)
(* The set of all operations.                                        *)
(* In this specification, we will focus on "Ins" and "Del".          *)
(*********************************************************************)
Op == [type: {"Rd"}] \cup \* a read specifies no arguments
      [type: {"Del"}, pos: Nat \ {0}] \cup \* a deletion specifies a position (from 1)
      [type: {"Ins", "Set"}, pos: Nat \ {0}, ch: Char] \* an insertion or a set specifies a position (from 1) and a character
Nop == CHOOSE v : v \notin Op  \* Nop: an operation representing "doing nothing"
-----------------------------------------------------------------------------
(*********************************************************************)
(* The "Apply" operator which applies an operation op on the list l. *)
(*********************************************************************)
Apply(op, l) == 
    LET len == Len(l) 
        pos == op.pos 
    IN CASE op.type = "Del" -> SubSeq(l, 1, pos - 1) \o SubSeq(l, pos + 1, len) 
        []  op.type = "Ins" -> Append(SubSeq(l, 1, pos - 1), op.ch) \o SubSeq(l, pos + 1, len)
=============================================================================
\* Modification History
\* Last modified Sat Jun 23 21:09:16 CST 2018 by hengxin
\* Created Sat Jun 23 20:56:53 CST 2018 by hengxin