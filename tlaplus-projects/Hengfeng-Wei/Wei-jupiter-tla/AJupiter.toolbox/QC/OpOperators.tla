---------------------------- MODULE OpOperators ----------------------------
EXTENDS Naturals, SequenceUtils
-----------------------------------------------------------------------------
Nop == PickNone(Nat)

Apply(op, l) == \* Apply an operation op on the list l.
    CASE op = Nop -> l
     []  op.type = "Rd" -> l
     []  op.type = "Del" -> DeleteElement(l, op.pos) \* Last(l) is deleted if pos > Len(l)
     []  op.type = "Ins" -> InsertElement(l, op.ch, op.pos) \* Append(l, ch) if pos > Len(l)
=============================================================================
\* Modification History
\* Last modified Wed Jan 02 14:34:47 CST 2019 by hengxin
\* Created Tue Aug 28 14:58:54 CST 2018 by hengxin