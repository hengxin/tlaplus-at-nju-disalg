--------------------------------- MODULE OT ---------------------------------
(***************************************************************************)
(* Specification of OT (Operational Transformation) functions.             *)
(* It consists of the basic OT functions for two operations and            *)
(* more general ones involving operation sequences.                        *)
(***************************************************************************)
EXTENDS Op, TLC
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
-----------------------------------------------------------------------------
(***************************************************************************)
(* The CP1 (Convergence) Property.                                         *)
(***************************************************************************)
CP1 == 
    \A l \in List, op1 \in Op, op2 \in Op: 
        \* /\ PrintT(ToString(l) \o ", " \o ToString(op1) \o ", " \o ToString(op2))
             \* It is not allowed to delete elements from an empty list.
        /\ \/ (l = <<>> /\ (op1.type = "Del" \/ op2.type = "Del")) 
             \* Priorities of two Insertions cannot be the same.
           \/ (op1.type = "Ins" /\ op2.type = "Ins" /\ op1.pr = op2.pr)
             \* Position of an insertion cannot be too large.
           \/ (op1.type = "Ins" /\ op1.pos > Len(l) + 1) 
           \/ (op2.type = "Ins" /\ op2.pos > Len(l) + 1) 
             \* Position of a deletion cannot be too large.
           \/ (op1.type = "Del" /\ op1.pos > Len(l)) 
           \/ (op2.type = "Del" /\ op2.pos > Len(l)) 
             \* The CP1 itself.
           \/ ApplyOps(<<op1, Xform(op2, op1)>>, l) = ApplyOps(<<op2, Xform(op1, op2)>>, l)
=============================================================================
\* Modification History
\* Last modified Wed Jul 04 22:08:22 CST 2018 by hengxin
\* Created Sun Jun 24 15:57:48 CST 2018 by hengxin