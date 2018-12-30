--------------------------------- MODULE OT ---------------------------------
(***************************************************************************)
(* Specification of OT (Operational Transformation) functions.             *)
(* It consists of the basic OT functions for two operations and            *)
(* more general ones involving operation sequences.                        *)
(***************************************************************************)
EXTENDS OpOperators, SetUtils
-----------------------------------------------------------------------------
(***************************************************************************)
(* OT (Operational Transformation) functions.                              *)
(*                                                                         *)
(* Naming convention: I for "Ins" and D for "Del".                         *)
(***************************************************************************)

(***************************************************************************)
(* The left "Ins" lins transformed against the right "Ins" rins.           *)
(***************************************************************************)
XformII(lins, rins) == 
    IF lins.pos < rins.pos
    THEN lins
    ELSE IF lins.pos > rins.pos
         THEN [lins EXCEPT !.pos = @ + 1]
         ELSE IF lins.ch = rins.ch
              THEN Nop
              ELSE IF lins.pr > rins.pr
                   THEN [lins EXCEPT !.pos = @+1]
                   ELSE lins
(***************************************************************************)
(* The left "Ins" ins transformed against the right "Del" del.             *)
(***************************************************************************)
XformID(ins, del) == 
    IF ins.pos <= del.pos
    THEN ins
    ELSE [ins EXCEPT !.pos = @-1]
(***************************************************************************)
(* The left "Del" del transformed against the right "Ins" ins.             *)
(***************************************************************************)
XformDI(del, ins) == 
    IF del.pos < ins.pos
    THEN del
    ELSE [del EXCEPT !.pos = @+1]
(***************************************************************************)
(* The left "Del" ldel transformed against the right "Del" rdel.           *)
(***************************************************************************)
XformDD(ldel, rdel) == 
    IF ldel.pos < rdel.pos
    THEN ldel
    ELSE IF ldel.pos > rdel.pos
         THEN [ldel EXCEPT !.pos = @-1]
         ELSE Nop
-----------------------------------------------------------------------------
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
-----------------------------------------------------------------------------
(***************************************************************************)
(* Generalized OT functions on operation sequences.                        *)
(***************************************************************************)

(***************************************************************************)
(* Iteratively/recursively transforms the operation op                     *)
(* against an operation sequence ops.                                      *)
(***************************************************************************)
RECURSIVE XformOpOps(_, _, _)
XformOpOps(xform(_,_), op, ops) == 
    IF ops = <<>> 
    THEN op 
    ELSE XformOpOps(xform, xform(op, Head(ops)), Tail(ops))
(***************************************************************************)
(* Iteratively/recursively transforms the operation op                     *)
(* against an operation sequence ops.                                      *)
(* Being different from XformOpOps,                                        *)
(* XformOpOpsX maintains the intermediate transformed operation            *)
(***************************************************************************)
RECURSIVE XformOpOpsX(_, _,_)
XformOpOpsX(xform(_, _), op, ops) == 
    IF ops = <<>> 
    THEN <<op>> 
    ELSE <<op>> \o XformOpOpsX(xform, xform(op, Head(ops)), Tail(ops))
(***************************************************************************)
(* Iteratively/recursively transforms the operation sequence ops           *)
(* against an operation op.                                                *)
(***************************************************************************)
XformOpsOp(xform(_, _), ops, op) == 
    LET opX == XformOpOpsX(xform, op, ops)
    IN  [i \in 1 .. Len(ops) |-> xform(ops[i], opX[i])]
(***************************************************************************)
(* Iteratively/recursively transforms an operation sequence ops1           *)
(* against another operation sequence ops2.                                *)
(*                                                                         *)
(* See also Definition 2.13 of the paper "Imine @ TCS06".                  *)
(***************************************************************************)
RECURSIVE XformOpsOps(_, _,_)
XformOpsOps(xform(_, _), ops1, ops2) ==
    IF ops2 = <<>>
    THEN ops1
    ELSE XformOpsOps(xform, XformOpsOp(xform, ops1, Head(ops2)), Tail(ops2))
=============================================================================
\* Modification History
\* Last modified Fri Dec 28 14:58:58 CST 2018 by hengxin
\* Created Sun Jun 24 15:57:48 CST 2018 by hengxin