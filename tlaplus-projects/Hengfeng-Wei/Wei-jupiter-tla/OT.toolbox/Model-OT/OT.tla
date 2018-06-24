--------------------------------- MODULE OT ---------------------------------
(***************************************************************************)
(* Specification of OT (Operational Transformation) functions.             *)
(***************************************************************************)
EXTENDS Op

(***************************************************************************)
(* OT (Operational Transformation) functions.                              *)
(* Naming convention: I for "Ins" and D for "Del".                         *)
(***************************************************************************)
XformII(lins, rins) == \* the left "Ins" lins transformed against the right "Ins" rins 
    IF lins.pos < rins.pos
    THEN lins
    ELSE IF lins.pos > rins.pos
         THEN [lins EXCEPT !.pos = @ + 1]
         ELSE IF lins.ch = rins.ch
              THEN Nop
              ELSE IF lins.pr > rins.pr
                   THEN [lins EXCEPT !.pos = @+1]
                   ELSE lins

XformID(ins, del) == \* the left "Ins" lins transformed against the right "Del" rdel
    IF ins.pos < del.pos
    THEN ins
    ELSE [ins EXCEPT !.pos = @-1]
                
XformDI(del, ins) == \* the left "Del" ldel transformed against the right "Ins" rins
    IF del.pos < ins.pos
    THEN del
    ELSE [del EXCEPT !.pos = @+1]
    
XformDD(ldel, rdel) == \* the left "Del" ldel transformed against the right "Del" rdel
    IF ldel.pos < rdel.pos
    THEN ldel
    ELSE IF ldel.pos > rdel.pos
         THEN [ldel EXCEPT !.pos = @-1]
         ELSE Nop
(***************************************************************************)
(* Transform the left operation lop against the right operation rop        *)
(* with appropriate OT function.                                           *)
(***************************************************************************)
Xform(lop, rop) == 
    CASE lop = Nop \/ rop = Nop -> lop
       []  lop.type = "Ins" /\ rop.type = "Ins" -> XformII(lop, rop)
       []  lop.type = "Ins" /\ rop.type = "Del" -> XformID(lop, rop)
       []  lop.type = "Del" /\ rop.type = "Ins" -> XformDI(lop, rop)
       []  lop.type = "Del" /\ rop.type = "Del" -> XformDD(lop, rop)
(***************************************************************************)
(* Iteratively/recursively transforms the operation op                     *)
(* against an operation sequence ops.                                      *)
(***************************************************************************)
RECURSIVE XformOpOps(_,_)
XformOpOps(op, ops) == 
    IF ops = <<>>
        THEN op
        ELSE XformOpOps(Xform(op, Head(ops)), Tail(ops))
(***************************************************************************)
(* Iteratively/recursively transforms the operation op                     *)
(* against an operation sequence ops.                                      *)
(* Different from XformOpOps,                                              *)
(* XformOpOpsX maintains the intermediate transformed operation            *)
(***************************************************************************)
RECURSIVE XformOpOpsX(_,_)
XformOpOpsX(op, ops) == 
    IF ops = <<>>
        THEN <<op>>
        ELSE <<op>> \o XformOpOpsX(Xform(op, Head(ops)), Tail(ops))
(***************************************************************************)
(* Iteratively/recursively transforms the operation sequence ops           *)
(* against an operation op.                                                *)
(***************************************************************************)
XformOpsOp(ops, op) == 
    LET opX == XformOpOpsX(op, ops)
    IN  [i \in 1 .. Len(ops) |-> Xform(ops[i], opX[i])]
======================================================]=======================
\* Modification History
\* Last modified Sun Jun 24 18:01:06 CST 2018 by hengxin
\* Created Sun Jun 24 15:57:48 CST 2018 by hengxin