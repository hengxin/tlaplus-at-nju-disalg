----------------------------- MODULE JupiterCtx -----------------------------
(*
Definitions and operators for context-based Jupiter protocols,
including AbsJupiter, XJupiter, and CJupiter.
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
\* Last modified Thu Dec 06 10:37:41 CST 2018 by hengxin
\* Created Wed Dec 05 20:03:50 CST 2018 by hengxin