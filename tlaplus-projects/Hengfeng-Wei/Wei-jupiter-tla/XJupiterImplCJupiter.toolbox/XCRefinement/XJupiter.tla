------------------------------ MODULE XJupiter ------------------------------
(*
Specification of the Jupiter protocol described in CSCW'2014 by Xu, Sun, and Li.
*)
EXTENDS GraphStateSpace
-----------------------------------------------------------------------------
VARIABLES
    c2ss,  \* c2ss[c]: the 2D state space (2ss, for short) at client c \in Client
    s2ss   \* s2ss[c]: the 2D state space maintained by the Server for client c \in Client

vars == <<intVars, ctxVars, c2ss, s2ss>>
-----------------------------------------------------------------------------
TypeOK == 
    /\ TypeOKInt
    /\ TypeOKCtx
    /\ \A c \in Client: IsSS(c2ss[c]) /\ IsSS(s2ss[c])
-----------------------------------------------------------------------------
Init == 
    /\ InitInt
    /\ InitCtx
    /\ c2ss = [c \in Client |-> EmptySS]
    /\ s2ss = [c \in Client |-> EmptySS]
-----------------------------------------------------------------------------
NextEdge(r, u, ss) == \* Return the unique outgoing edge from u in 2D state space ss
    CHOOSE e \in ss.edge: e.from = u \* before a transformation at u (r is not used).

ClientPerform(c, cop) == 
    LET xform == xForm(NextEdge, c, cop, c2ss[c]) \* xform: [xcop, xss, lss]
    IN  /\ c2ss' = [c2ss EXCEPT ![c] = @ (+) xform.xss]
        /\ SetNewAop(c, xform.xcop.op)

ServerPerform(cop) == 
    LET c == ClientOf(cop)
    xform == xForm(NextEdge, Server, cop, s2ss[c]) \* xform: [xcop, xss, lss]
     xcop == xform.xcop
    IN  /\ s2ss' = [cl \in Client |-> IF cl = c 
                                      THEN s2ss[cl] (+) xform.xss 
                                      ELSE s2ss[cl] (+) xform.lss]
        /\ SetNewAop(Server, xcop.op)
        /\ Comm!SSendSame(c, xcop)  \* broadcast the transformed xcop 
-----------------------------------------------------------------------------
DoOp(c, op) == 
    LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq[c]], ctx |-> ds[c]] 
    IN  /\ ClientPerform(c, cop)
        /\ Comm!CSend(cop)

Do(c) == 
    /\ DoInt(DoOp, c)
    /\ DoCtx(c)
    /\ UNCHANGED s2ss

Rev(c) == 
    /\ RevInt(ClientPerform, c)
    /\ RevCtx(c)
    /\ UNCHANGED s2ss

SRev == 
    /\ SRevInt(ServerPerform)
    /\ SRevCtx
    /\ UNCHANGED c2ss
-----------------------------------------------------------------------------
Next == 
    \/ \E c \in Client: Do(c) \/ Rev(c)
    \/ SRev

Fairness == 
    WF_vars(SRev \/ \E c \in Client: Rev(c))

Spec == Init /\ [][Next]_vars \* /\ Fairness
-----------------------------------------------------------------------------
CSSync == \* Each client c \in Client is synchonized with the Server.
    \forall c \in Client: (ds[c] = ds[Server]) => c2ss[c] = s2ss[c]
    
THEOREM Spec => []CSSync
=============================================================================
\* Modification History
\* Last modified Sat Jan 12 15:57:05 CST 2019 by hengxin
\* Created Tue Oct 09 16:33:18 CST 2018 by hengxin