----------------------------- MODULE JupiterCtx -----------------------------
(*
Definitions and operators for context-based Jupiter protocols,
including AbsJupiter, CJupiter, and XJupiter.
*)
EXTENDS JupiterInterface
-----------------------------------------------------------------------------
VARIABLES
    cseq,  \* cseq[c]: local sequence number at client c \in Client
    ds     \* ds[r]: document state (a set of Oids) of replica r \in Replica

ctxVars == <<cseq, ds>>
-----------------------------------------------------------------------------
Oid == [c: Client, seq: Nat]  \* operation identifier
Cop == [op: Op \cup {Nop}, oid: Oid, ctx: SUBSET Oid] \* contexted-based op

ClientOf(cop) == cop.oid.c

COT(lcop, rcop) == \* OT of two Cop(s).                                 
    [lcop EXCEPT !.op = Xform(lcop.op, rcop.op), !.ctx = @ \cup {rcop.oid}]

UpdateDS(r, cop) == \* update ds to include new Cop (in terms of oid)
    ds' = [ds EXCEPT ![r] = @ \cup {cop.oid}]
-----------------------------------------------------------------------------
TypeOKCtx ==
    /\ cseq \in [Client -> Nat]
    /\ ds \in [Replica -> SUBSET Oid]

InitCtx ==
    /\ cseq = [c \in Client |-> 0]
    /\ ds = [r \in Replica |-> {}]
    
DoCtx(c) ==
    /\ cseq' = [cseq EXCEPT ![c] = @ + 1]
    \* /\ don't know the generated cop; no way to update ds

RevCtx(c) ==
    /\ UpdateDS(c, Head(cincoming[c]))
    /\ UNCHANGED cseq
    
SRevCtx ==
    /\ UpdateDS(Server, Head(sincoming))
    /\ UNCHANGED cseq
=============================================================================
\* Modification History
\* Last modified Wed Dec 19 18:05:26 CST 2018 by hengxin
\* Created Wed Dec 05 20:03:50 CST 2018 by hengxin