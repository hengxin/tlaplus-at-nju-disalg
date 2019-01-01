----------------------------- MODULE AbsJupiter -----------------------------
(*
Abstract Jupiter, inspired by the COT algorithm proposed by Sun and Sun; see TPDS'2009.
*)
EXTENDS JupiterSerial
-----------------------------------------------------------------------------
VARIABLES
    copss   \* copss[r]: the state space (i.e., a set) of Cops maintained at replia r \in Replica
    
vars == <<intVars, ctxVars, serialVars, copss>>
-----------------------------------------------------------------------------
TypeOK ==
    /\ TypeOKInt
    /\ TypeOKCtx
    /\ TypeOKSerial
    /\ Comm(Cop)!TypeOK
    /\ copss \in [Replica -> SUBSET Cop]
-----------------------------------------------------------------------------
Init ==
    /\ InitInt
    /\ InitCtx
    /\ InitSerial
    /\ Comm(Cop)!Init
    /\ copss = [r \in Replica |-> {}]
-----------------------------------------------------------------------------
RECURSIVE xForm(_, _)
xForm(cop, r) ==
    LET ctxDiff == ds[r] \ cop.ctx  \* THEOREM: cop.ctx \subseteq ds[r]
        RECURSIVE xFormHelper(_, _, _)
        xFormHelper(coph, ctxDiffh, copssr) == \* copssr: state space generated during transformation
            IF ctxDiffh = {} THEN [xcop |-> coph, xcopss |-> copssr]
            ELSE LET foph == CHOOSE op \in ctxDiffh: \* the first op in serial
                                \A opprime \in ctxDiffh \ {op}: tb(op, opprime, serial[r])
                     fcophDict == {op \in copssr: op.oid = foph /\ op.ctx = coph.ctx}
                     fcoph == CHOOSE op \in fcophDict: TRUE \* THEOREM: Cardinality(fophDict) = 1
                     xcoph == COT(coph, fcoph)
                     xfcoph == COT(fcoph, coph)
                  IN xFormHelper(xcoph, ctxDiffh \ {foph}, copssr \cup {xcoph, xfcoph})
     IN xFormHelper(cop, ctxDiff, copss[r]) 

Perform(cop, r) ==
    LET xform == xForm(cop, r)  \* [xcop, xcopss] 
     IN /\ copss' = [copss EXCEPT ![r] = xform.xcopss \cup {cop}]
        /\ aop' = xform.xcop.op
-----------------------------------------------------------------------------
DoOp(c, op) == \* Client c \in Client processes a locally generated operation op.
    LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq'[c]], ctx |-> ds[c]]
     IN /\ Perform(cop, c)
        /\ Comm(Cop)!CSend(cop)

Do(c) == 
    /\ DoCtx(c)
    /\ DoSerial(c)
    /\ DoInt(DoOp, c)

Rev(c) ==
    /\ Comm(Cop)!CRev(c)
    /\ Perform(Head(cincoming[c]), c)
    /\ RevSerial(c)
    /\ RevCtx(c)
    /\ RevInt(c)

SRev ==
    /\ Comm(Cop)!SRev
    /\ LET cop == Head(sincoming)
        IN /\ Perform(cop, Server)
           /\ Comm(Cop)!SSendSame(cop.oid.c, cop)
    /\ SRevSerial
    /\ SRevCtx
    /\ SRevInt
-----------------------------------------------------------------------------
Next ==
    \/ \E c \in Client: Do(c) \/ Rev(c)
    \/ SRev

Fairness ==
    WF_vars(SRev \/ \E c \in Client: Rev(c))

Spec == Init /\ [][Next]_vars \* /\ Fairness
-----------------------------------------------------------------------------
Compactness == 
    Comm(Cop)!EmptyChannel => Cardinality(Range(copss)) = 1
    
THEOREM Spec => Compactness
=============================================================================
\* Modification History
\* Last modified Tue Jan 01 11:22:36 CST 2019 by hengxin
\* Created Wed Dec 05 19:55:52 CST 2018 by hengxin