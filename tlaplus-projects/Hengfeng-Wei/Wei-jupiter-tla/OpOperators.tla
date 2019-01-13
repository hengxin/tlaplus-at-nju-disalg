---------------------------- MODULE OpOperators ----------------------------
EXTENDS Naturals, SequenceUtils
-----------------------------------------------------------------------------
Nop == PickNone(Nat)

Apply(op, l) == \* Apply operation op on list l.
    CASE op = Nop -> l
      [] op.type = "Rd" -> l
      [] op.type = "Del" -> DeleteElement(l, op.pos)
      [] op.type = "Ins" -> InsertElement(l, op.ch, op.pos) \* append to the end
                                                            \* if op.pos = Len(l) + 1
=============================================================================
\* Modification History
\* Last modified Sat Jan 12 21:41:22 CST 2019 by hengxin
\* Created Tue Aug 28 14:58:54 CST 2018 by hengxin