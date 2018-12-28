-------------------------------- MODULE OTMC --------------------------------
(***************************************************************************)
(* Model checking the OT functions defined in the OT module.               *)
(*                                                                         *)
(* The OT functions are expected to satisfy both the CP1 property and the  *)
(* generalized CP1 property.                                               *)
(***************************************************************************)
EXTENDS OT, TLC, AdditionalSequenceOperators

(***************************************************************************)
(* Constants for finite/bounded model checking.                            *)
(***************************************************************************)
CONSTANTS  MaxPr,  \* max priority
           MaxLen  \* max length of list
            
ASSUME /\ MaxPr \in PosInt
       /\ MaxLen \in Nat

ListMaxLen == SeqMaxLen(Char, MaxLen)
-----------------------------------------------------------------------------
(***************************************************************************)
(* The CP1 (C for Convergence) property.                                   *)
(*                                                                         *)
(* TODO: refactor the generation of op1 and op2.                           *)
(***************************************************************************)

(*********************************************************************)
(* Legal operations with respect to a list l.                        *)
(*********************************************************************)
InsOp(l) ==  \* Position of an insertion cannot be too large.
    [type: {"Ins"}, pos: 1 .. Len(l) + 1, ch: Char, pr: 1 .. MaxPr]

DelOp(l) == 
    IF l = <<>> 
    THEN {} \* Not allowed to delete elements from an empty list.
    ELSE  [type: {"Del"}, pos: 1 .. Len(l)] \* Position of a deletion cannot be too large.
OpOnList(l) == InsOp(l) \cup DelOp(l)

CP1 == 
    \A l \in ListMaxLen: 
        \A op1 \in OpOnList(l), op2 \in OpOnList(l): 
            \* /\ PrintT(ToString(l) \o ", " \o ToString(op1) \o ", " \o ToString(op2))
            /\ \* Priorities of these two insertions cannot be the same.
               \/ (op1.type = "Ins" /\ op2.type = "Ins" /\ op1.pr = op2.pr)
                 \* The CP1 itself.
               \/ ApplyOps(<<op1, Xform(op2, op1)>>, l) = ApplyOps(<<op2, Xform(op1, op2)>>, l)

(***************************************************************************)
(* The generalized CP1 (C for Convergence) property.                       *)
(*                                                                         *)
(* See also Theorem 2.14 of the paper "Imine @ TCS06".                     *)
(*                                                                         *)
(* FIXME: Generate legal operation sequences.                              *)
(***************************************************************************)
GCP1 ==
    \A l \in ListMaxLen, ops1 \in SeqMaxLen(Op, 1), ops2 \in SeqMaxLen(Op, 1):
        \* \/ (Head(ops1).type = "Del" \/ Head(ops2).type = "Del")
        \/ ApplyOps(ops1 \o XformOpsOps(ops2, ops1), l) = 
           ApplyOps(ops2 \o XformOpsOps(ops1, ops2), l)
=============================================================================
\* Modification History
\* Last modified Sat Jul 07 13:36:50 CST 2018 by hengxin
\* Created Sat Jul 07 13:31:57 CST 2018 by hengxin