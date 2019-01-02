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
    /\ copss \in [Replica -> SUBSET Cop]
-----------------------------------------------------------------------------
Init ==
    /\ InitInt
    /\ InitCtx
    /\ InitSerial
    /\ copss = [r \in Replica |-> {}]
-----------------------------------------------------------------------------
RECURSIVE xForm(_, _)
xForm(r, cop) ==
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

Perform(r, cop) ==
    LET xform == xForm(r, cop)  \* [xcop, xcopss] 
     IN /\ copss' = [copss EXCEPT ![r] = xform.xcopss \cup {cop}]
        /\ SetNewAop(r, xform.xcop.op)
        
ServerPerform(cop) == 
    /\ Perform(Server, cop)
    /\ Comm!SSendSame(ClientOf(cop), cop)
-----------------------------------------------------------------------------
DoOp(c, op) ==
    LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq[c]], ctx |-> ds[c]]
     IN /\ Perform(c, cop)
        /\ Comm!CSend(cop)

Do(c) == 
    /\ DoInt(DoOp, c)
    /\ DoCtx(c)
    /\ DoSerial(c)

Rev(c) ==
    /\ RevInt(Perform, c)
    /\ RevCtx(c)
    /\ RevSerial(c)

SRev ==
    /\ SRevInt(ServerPerform)
    /\ SRevCtx
    /\ SRevSerial
-----------------------------------------------------------------------------
Next ==
    \/ \E c \in Client: Do(c) \/ Rev(c)
    \/ SRev

Fairness ==
    WF_vars(SRev \/ \E c \in Client: Rev(c))

Spec == Init /\ [][Next]_vars \* /\ Fairness
-----------------------------------------------------------------------------
Compactness == 
    Comm!EmptyChannel => Cardinality(Range(copss)) = 1
    
THEOREM Spec => Compactness
=============================================================================
\* Modification History
\* Last modified Wed Jan 02 20:47:48 CST 2019 by hengxin
\* Created Wed Dec 05 19:55:52 CST 2018 by hengxin