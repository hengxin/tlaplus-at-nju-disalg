-------------------------- MODULE BufferStateSpace --------------------------
(*
The buffer (i.e., sequence) representation of state space used in AJupiter.
This module defines generalized OT functions on operation sequences.
*)
EXTENDS Naturals, SequenceUtils
-----------------------------------------------------------------------------
RECURSIVE xFormOpOps(_, _,_) \* Transform op against an operation sequence ops. 
xFormOpOps(xform(_, _), op, ops) == 
    IF ops = <<>> THEN <<op>> \* Maintain and return the intermediate transformed operations.
    ELSE <<op>> \o xFormOpOps(xform, xform(op, Head(ops)), Tail(ops))

xFormOpsOp(xform(_, _), ops, op) == \* Transform an operation sequence ops against op.
    LET opX == xFormOpOps(xform, op, ops)
    IN  [i \in 1 .. Len(ops) |-> xform(ops[i], opX[i])]

xFormFull(xform(_, _), op, ops) == 
    [xop |-> Last(xFormOpOps(xform, op, ops)),
    xops |-> xFormOpsOp(xform, ops, op)]

xFormShift(xform(_, _), op, ops, shift) == \* shift of ops
    xFormFull(xform, op, SubSeq(ops, shift + 1, Len(ops)))
=============================================================================
\* Modification History
\* Last modified Thu Jan 17 10:30:18 CST 2019 by hengxin
\* Created Sat Jan 12 14:55:34 CST 2019 by hengxin