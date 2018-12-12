----------------------------- MODULE JupiterCtx -----------------------------
(*
Definitions and operators for context-based Jupiter protocols,
including AbsJupiter, CJupiter, and XJupiter.
*)
EXTENDS JupiterInterface
-----------------------------------------------------------------------------
(* 
Cop: operation of type Op with context                            
*)
Oid == [c: Client, seq: Nat]  \* operation identifier
Cop == [op: Op \cup {Nop}, oid: Oid, ctx: SUBSET Oid]
(* 
OT of two operations of type Cop.                                 
*)
COT(lcop, rcop) == [lcop EXCEPT !.op = Xform(lcop.op, rcop.op), !.ctx = @ \cup {rcop.oid}]
=============================================================================
\* Modification History
\* Last modified Wed Dec 12 20:11:40 CST 2018 by hengxin
\* Created Wed Dec 05 20:03:50 CST 2018 by hengxin