-------------------------- MODULE BufferStateSpace --------------------------
(*
The buffer (i.e., sequence) representation of state space used in AJupiter.
This module defines generalized OT functions on operation sequences.
*)
EXTENDS Integers, Sequences
-----------------------------------------------------------------------------
RECURSIVE xFormOpOps(_, _, _) \* Transform op against an operation sequence ops.
xFormOpOps(xform(_,_), op, ops) == 
    IF ops = <<>> 
    THEN op 
    ELSE xFormOpOps(xform, xform(op, Head(ops)), Tail(ops))

RECURSIVE xFormOpOpsX(_, _,_) \* Transform op against an operation sequence ops. 
xFormOpOpsX(xform(_, _), op, ops) == 
    IF ops = <<>> 
    THEN <<op>> \* Maintain and return the intermediate transformed operations.
    ELSE <<op>> \o xFormOpOpsX(xform, xform(op, Head(ops)), Tail(ops))

xFormOpsOp(xform(_, _), ops, op) == \* Transform an operation sequence ops against op.
    LET opX == xFormOpOpsX(xform, op, ops)
    IN  [i \in 1 .. Len(ops) |-> xform(ops[i], opX[i])]

xFormShift(xform(_, _), op, ops, shift) ==
    LET shiftedOps == SubSeq(ops, shift, Len(ops))
    IN  [xop |-> xFormOpOps(xform, op, shiftedOps),
        xops |-> xFormOpsOp(xform, shiftedOps, op)]
=============================================================================
\* Modification History
\* Last modified Sat Jan 12 20:53:57 CST 2019 by hengxin
\* Created Sat Jan 12 14:55:34 CST 2019 by hengxin