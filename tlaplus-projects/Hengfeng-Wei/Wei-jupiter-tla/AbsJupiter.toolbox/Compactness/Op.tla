---------------------------- MODULE Op ----------------------------
(*
Definition and operator for list operations.
*)
EXTENDS SystemModel
-----------------------------------------------------------------------------
Rd == [type: {"Rd"}]
Del == [type: {"Del"}, pos: 1 .. MaxLen] \* The positions (pos) are indexed from 1.
Ins == [type: {"Ins"}, pos: 1 .. (MaxLen + 1), ch: Char, pr: Range(Priority)]

Op == Ins \cup Del  \* The set of all operations (now we don't consider Rd operations).

Nop == PickNone(Op)

Apply(op, l) == \* Apply operation op on list l.
    CASE op = Nop -> l
      [] op.type = "Rd" -> l
      [] op.type = "Del" -> DeleteElement(l, op.pos)
      [] op.type = "Ins" -> InsertElement(l, op.ch, op.pos) \* append to the end
                                                            \* if op.pos = Len(l) + 1
=============================================================================
\* Modification History
\* Last modified Mon Jan 14 09:36:21 CST 2019 by hengxin
\* Created Tue Aug 28 14:58:54 CST 2018 by hengxin