---------------------------- MODULE OpOperators ----------------------------
(***************************************************************************)
(* Operators for Op.                                                       *)
(***************************************************************************)

EXTENDS Naturals, Sequences, AdditionalSequenceOperators

Nop == PickNone(Nat)
-----------------------------------------------------------------------------
(*********************************************************************)
(* The "Apply" operator which applies an operation op on the list l. *)
(*                                                                   *)
(* Del: If pos > Len(l), the last element of l is deleted.           *)
(*      This is realized by the DeleteElement operator.              *)
(* Ins: If pos > Len(l), the new element is appended to l.           *)
(*      This is realized by the InsertElement operator.              *)
(*********************************************************************)
Apply(op, l) == CASE op = Nop -> l
                 [] op.type = "Rd" -> l
                 [] op.type = "Del" -> DeleteElement(l, op.pos)
                 [] op.type = "Ins" -> InsertElement(l, op.ch, op.pos)

(*********************************************************************)
(* The "ApplyOps" operator which applies an operation sequence ops   *)
(* on the list l.                                                    *)
(*********************************************************************)
RECURSIVE ApplyOps(_, _)
ApplyOps(ops, l) ==
    IF ops = <<>>
    THEN l
    ELSE Apply(Last(ops), ApplyOps(AllButLast(ops), l))
-----------------------------------------------------------------------------
(*********************************************************************)
(* Check whether an operation op is legal with respect to the list l.*)
(*********************************************************************)
IsLegalOp(op, l) == CASE op.type = "Del" -> op.pos <= Len(l)
                     []  op.type = "Ins" -> op.pos <= Len(l) + 1
=============================================================================
\* Modification History
\* Last modified Tue Aug 28 15:51:36 CST 2018 by hengxin
\* Created Tue Aug 28 14:58:54 CST 2018 by hengxin