------------------------------ MODULE CJupiter ------------------------------
(*
Specification of our own CJupiter protocol; see Wei@OPODIS'2018.
*)
EXTENDS StateSpace, JupiterSerial
-----------------------------------------------------------------------------
VARIABLES
    css    \* css[r]: the n-ary ordered state space at replica r \in Replica

vars == <<intVars, ctxVars, serialVars, css>>
-----------------------------------------------------------------------------
TypeOK == 
    /\ TypeOKInt
    /\ TypeOKCtx
    /\ TypeOKSerial
    /\ \A r \in Replica: IsSS(css[r])
-----------------------------------------------------------------------------
Init == 
    /\ InitInt
    /\ InitCtx
    /\ InitSerial
    /\ css = [r \in Replica |-> EmptySS]
-----------------------------------------------------------------------------
(*
Iteratively transform cop with a path in the css 
at replica r \in Replica, following the first edges.
*)
xForm(r, cop) ==
    LET rcss == css[r]
        u == Locate(cop, rcss)
        v == u \cup {cop.oid}
        RECURSIVE xFormHelper(_, _, _, _)
        xFormHelper(uh, vh, coph, xcss) == \* xcss: eXtra css created during transformation
            IF uh = ds[r] THEN [xcss |-> xcss, xcop |-> coph]
            ELSE LET fedge == \* the first edge
                        CHOOSE e \in rcss.edge: 
                            /\ e.from = uh 
                            /\ \A uhe \in rcss.edge \ {e}: 
                                (uhe.from = uh) => tb(e.cop.oid, uhe.cop.oid, serial[r])
                     uprime == fedge.to
                     fcop == fedge.cop
                     coph2fcop == COT(coph, fcop)
                     fcop2coph == COT(fcop, coph)
                     vprime == vh \cup {fcop.oid}
                  IN xFormHelper(uprime, vprime, coph2fcop,
                        xcss (+) [node |-> {vprime},
                                  edge |-> {[from |-> vh, to |-> vprime, cop |-> fcop2coph],
                                            [from |-> uprime, to |-> vprime, cop |-> coph2fcop]}])
     IN xFormHelper(u, v, cop, [node |-> {v}, edge |-> {[from |-> u, to |-> v, cop |-> cop]}])

Perform(r, cop) == 
    LET xform == xForm(r, cop)  \* xform: [xcss, xcop]
     IN /\ css' = [css EXCEPT ![r] = @ (+) xform.xcss]
        /\ SetNewAop(r, xform.xcop.op)

ServerPerform(cop) ==
    /\ Perform(Server, cop)
    /\ Comm!SSendSame(ClientOf(cop), cop)  \* broadcast the original operation
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
Compactness == \* Compactness of CJupiter: the CSSes at all replicas are the same.
    Comm!EmptyChannel => Cardinality(Range(css)) = 1

THEOREM Spec => Compactness
=============================================================================
\* Modification History
\* Last modified Thu Jan 03 16:35:20 CST 2019 by hengxin
\* Created Sat Sep 01 11:08:00 CST 2018 by hengxin