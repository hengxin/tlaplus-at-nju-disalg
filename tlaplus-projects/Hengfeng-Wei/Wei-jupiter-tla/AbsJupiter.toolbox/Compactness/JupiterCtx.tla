----------------------------- MODULE JupiterCtx -----------------------------
(*
Definitions and operators for context-based Jupiter protocols,
including AbsJupiter, CJupiter, and XJupiter.
*)
EXTENDS JupiterInterface
-----------------------------------------------------------------------------
VARIABLES
    cseq   \* cseq[c]: local sequence number at client c \in Client
    \* ds      \* ds[r]: document state (a set of Oids) of replica r \in Replica

ctxVars == <<cseq>>
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
-----------------------------------------------------------------------------
TypeOKCtx ==
    /\ cseq \in [Client -> Nat]

InitCtx ==
    /\ cseq = [c \in Client |-> 0]
    
DoCtx(c) ==
    /\ cseq' = [cseq EXCEPT ![c] = @ + 1]

RevCtx(c) ==
    /\ UNCHANGED cseq
    
SRevCtx ==
    /\ UNCHANGED cseq
=============================================================================
\* Modification History
\* Last modified Sat Dec 15 17:20:47 CST 2018 by hengxin
\* Created Wed Dec 05 20:03:50 CST 2018 by hengxin