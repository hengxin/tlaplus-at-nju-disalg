--------------------------------- MODULE OT ---------------------------------
(*
This module contains the basic OT (Operational Transformation) functions 
for two operations and general ones involving operation sequences.                       
*)
EXTENDS OpOperators, SetUtils
-----------------------------------------------------------------------------
XformII(lins, rins) == \* lins is transformed against rins
    IF lins.pos < rins.pos
    THEN lins
    ELSE IF lins.pos > rins.pos
         THEN [lins EXCEPT !.pos = @ + 1]
         ELSE IF lins.ch = rins.ch
              THEN Nop
              ELSE IF lins.pr > rins.pr
                   THEN [lins EXCEPT !.pos = @ + 1]
                   ELSE lins

XformID(ins, del) == \* ins is transformed against del
    IF ins.pos <= del.pos
    THEN ins
    ELSE [ins EXCEPT !.pos = @ - 1]

XformDI(del, ins) == \* del is transformed against ins
    IF del.pos < ins.pos
    THEN del
    ELSE [del EXCEPT !.pos = @ + 1]

XformDD(ldel, rdel) == \* ldel is transformed against rdel
    IF ldel.pos < rdel.pos
    THEN ldel
    ELSE IF ldel.pos > rdel.pos
         THEN [ldel EXCEPT !.pos = @ - 1]
         ELSE Nop

Xform(lop, rop) == \* lop is transformed against rop
    CASE lop = Nop \/ rop = Nop -> lop
       []  lop.type = "Ins" /\ rop.type = "Ins" -> XformII(lop, rop)
       []  lop.type = "Ins" /\ rop.type = "Del" -> XformID(lop, rop)
       []  lop.type = "Del" /\ rop.type = "Ins" -> XformDI(lop, rop)
       []  lop.type = "Del" /\ rop.type = "Del" -> XformDD(lop, rop)
-----------------------------------------------------------------------------
(*
Generalized OT functions on operation sequences.
*)
RECURSIVE XformOpOps(_, _, _) 
XformOpOps(xform(_,_), op, ops) == \* Transform an operation op against an operation sequence ops.
    IF ops = <<>> 
    THEN op 
    ELSE XformOpOps(xform, xform(op, Head(ops)), Tail(ops))

RECURSIVE XformOpOpsX(_, _,_)
XformOpOpsX(xform(_, _), op, ops) == \* Transform an operation op against an operation sequence ops. 
    IF ops = <<>> 
    THEN <<op>> \* Maintain and return the intermediate transformed operations.
    ELSE <<op>> \o XformOpOpsX(xform, xform(op, Head(ops)), Tail(ops))

XformOpsOp(xform(_, _), ops, op) == \* Transform an operation sequence ops against an operation op.
    LET opX == XformOpOpsX(xform, op, ops)
    IN  [i \in 1 .. Len(ops) |-> xform(ops[i], opX[i])]
(*
Transforms an operation sequence ops1 against another operation sequence ops2;                               
see Definition 2.13 of the paper "Imine@TCS06".
*)
RECURSIVE XformOpsOps(_, _,_)
XformOpsOps(xform(_, _), ops1, ops2) == 
    IF ops2 = <<>>
    THEN ops1
    ELSE XformOpsOps(xform, XformOpsOp(xform, ops1, Head(ops2)), Tail(ops2))
=============================================================================
\* Modification History
\* Last modified Wed Jan 02 14:26:19 CST 2019 by hengxin
\* Created Sun Jun 24 15:57:48 CST 2018 by hengxin