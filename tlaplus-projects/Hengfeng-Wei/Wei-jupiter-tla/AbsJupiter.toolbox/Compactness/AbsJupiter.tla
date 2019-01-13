----------------------------- MODULE AbsJupiter -----------------------------
(*
Abstract Jupiter, inspired by the COT algorithm proposed by Sun and Sun; see TPDS'2009.
*)
EXTENDS JupiterSerial, SetStateSpace
-----------------------------------------------------------------------------
VARIABLES
    copss   \* copss[r]: the state space (i.e., a set) of Cop maintained at replia r \in Replica
    
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
NextCop(r, cop, ss, ctx) == \* Return the next fcop \in Cop against which cop is to be transformed.
    LET foid == CHOOSE oid \in ctx: \* the first oid in ctx according to serial[r]
                    \A id \in ctx \ {oid}: tb(oid, id, serial[r])
    IN  CHOOSE fcop \in ss: \* THEOREM: Existence of fcop
            fcop.oid = foid /\ fcop.ctx = cop.ctx 

Perform(r, cop) ==
    LET xform == xForm(NextCop, r, cop, copss[r])  \* [xcop, xss] 
    IN  /\ copss' = [copss EXCEPT ![r] = xform.xss]
        /\ SetNewAop(r, xform.xcop.op)
        
ClientPerform(c, cop) == Perform(c, cop)
        
ServerPerform(cop) == 
    /\ Perform(Server, cop)
    /\ Comm!SSendSame(ClientOf(cop), cop)
-----------------------------------------------------------------------------
DoOp(c, op) ==
    LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq[c]], ctx |-> ds[c]]
    IN  /\ ClientPerform(c, cop)
        /\ Comm!CSend(cop)

Do(c) == 
    /\ DoInt(DoOp, c)
    /\ DoCtx(c)
    /\ DoSerial(c)

Rev(c) ==
    /\ RevInt(ClientPerform, c)
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
\* Last modified Thu Jan 10 08:34:12 CST 2019 by hengxin
\* Created Wed Dec 05 19:55:52 CST 2018 by hengxin