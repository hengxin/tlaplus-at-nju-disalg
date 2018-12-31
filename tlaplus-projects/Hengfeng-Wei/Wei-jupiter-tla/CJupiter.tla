------------------------------ MODULE CJupiter ------------------------------
(*
Model of our own CJupiter protocol.
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
    /\ Comm(Cop)!TypeOK
    /\ \A r \in Replica: IsSS(css[r])
-----------------------------------------------------------------------------
Init == 
    /\ InitInt
    /\ InitCtx
    /\ InitSerial
    /\ Comm(Cop)!Init
    /\ css = [r \in Replica |-> EmptySS]
-----------------------------------------------------------------------------
(*
xForm: Iteratively transform cop with a path through the css 
at replica r \in Replica, following the first edges.
*)
xForm(cop, r) ==
    LET rcss == css[r]
        u == Locate(cop, rcss)
        v == u \cup {cop.oid}
        RECURSIVE xFormHelper(_, _, _, _)
        xFormHelper(uh, vh, coph, xcss) == \* xcss: eXtra css created during transformation
            IF uh = ds[r] THEN [xcss |-> xcss, xcop |-> coph]
            ELSE LET fedge == CHOOSE e \in rcss.edge: 
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

Perform(cop, r) == \* Perform cop at replica r \in Replica.                             
    LET xform == xForm(cop, r)  \* xform: [xcss, xcop]
    IN /\ css' = [css EXCEPT ![r] = @ (+) xform.xcss]
       /\ state' = [state EXCEPT ![r] = Apply(xform.xcop.op, @)]
-----------------------------------------------------------------------------
DoOp(c, op) == 
    /\ LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq'[c]], ctx |-> ds[c]]
       IN  /\ Perform(cop, c)
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
       IN  /\ Perform(cop, Server)
           /\ Comm(Cop)!SSendSame(cop.oid.c, cop)  \* broadcast the original operation
    /\ SRevSerial
    /\ SRevCtx
    /\ SRevInt
-----------------------------------------------------------------------------
Next == 
    \/ \E c \in Client: Do(c) \/ Rev(c)
    \/ SRev

Fairness == \* There is no requirement that the clients ever generate operations.
    WF_vars(SRev \/ \E c \in Client: Rev(c))

Spec == Init /\ [][Next]_vars \* /\ Fairness (We care more about safety.)
-----------------------------------------------------------------------------
Compactness == \* Compactness of CJupiter: the CSSes at all replicas are the same.
    Comm(Cop)!EmptyChannel => Cardinality(Range(css)) = 1

THEOREM Spec => Compactness
=============================================================================
\* Modification History
\* Last modified Mon Dec 31 20:36:31 CST 2018 by hengxin
\* Created Sat Sep 01 11:08:00 CST 2018 by hengxin