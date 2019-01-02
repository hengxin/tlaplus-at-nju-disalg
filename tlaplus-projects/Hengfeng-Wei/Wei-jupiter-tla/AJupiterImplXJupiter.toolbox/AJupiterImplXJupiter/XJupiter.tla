------------------------------ MODULE XJupiter ------------------------------
(*
Specification of the Jupiter protocol described in CSCW'2014 by Xu, Sun, and Li.
We call it XJupiter, with 'X' for "Xu".
*)
EXTENDS StateSpace
-----------------------------------------------------------------------------
VARIABLES
    c2ss,   \* c2ss[c]: the 2D state space (2ss, for short) at client c \in Client
    s2ss    \* s2ss[c]: the 2D state space maintained by the Server for client c \in Client

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
xForm(cop, ss, cur) == \* Transform cop with an operation sequence in 2D state space ss.
    LET u == Locate(cop, ss)
        v == u \cup {cop.oid}
        RECURSIVE xFormHelper(_, _, _, _)
        xFormHelper(uh, vh, coph, xss) == \* xss: eXtra ss created during transformation
            IF uh = cur THEN [xss |-> xss, xcop |-> coph]
            ELSE LET e == CHOOSE e \in ss.edge: e.from = uh /\ ClientOf(e.cop) # ClientOf(cop)
                     copprime == e.cop
                     uprime == e.to
                     vprime == vh \cup {copprime.oid}
                     coph2copprime == COT(coph, copprime)
                     copprime2coph == COT(copprime, coph)
                  IN xFormHelper(uprime, vprime, coph2copprime,
                        xss (+) [node |-> {vprime},
                                 edge |-> {[from |-> vh, to |-> vprime, cop |-> copprime2coph], 
                                           [from |-> uprime, to |-> vprime, cop |-> coph2copprime]}])
     IN xFormHelper(u, v, cop, [node |-> {v}, edge |-> {[from |-> u, to |-> v, cop |-> cop]}])

ClientPerform(c, cop) == 
    LET xform == xForm(cop, c2ss[c], ds[c]) \* xform: [xss, xcop]
     IN /\ c2ss' = [c2ss EXCEPT ![c] = @ (+) xform.xss]
        /\ SetNewAop(c, xform.xcop.op)

ServerPerform(cop) == 
    LET c == ClientOf(cop)
     scur == ds[Server]
    xform == xForm(cop, s2ss[c], scur) \* xform: [xss, xcop]
     xcop == xform.xcop
     xcur == scur \cup {cop.oid}
     IN /\ s2ss' = [cl \in Client |-> 
                    IF cl = c 
                    THEN s2ss[cl] (+) xform.xss
                    ELSE s2ss[cl] (+) [node |-> {xcur}, 
                        edge |-> {[from |-> scur, to |-> xcur, cop |-> xcop]}]]
        /\ SetNewAop(Server, xcop.op)
        /\ Comm!SSendSame(c, xcop) 
-----------------------------------------------------------------------------
DoOp(c, op) == 
    LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq[c]], ctx |-> ds[c]] 
     IN /\ ClientPerform(c, cop)
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
\* Last modified Wed Jan 02 22:00:47 CST 2019 by hengxin
\* Created Tue Oct 09 16:33:18 CST 2018 by hengxin