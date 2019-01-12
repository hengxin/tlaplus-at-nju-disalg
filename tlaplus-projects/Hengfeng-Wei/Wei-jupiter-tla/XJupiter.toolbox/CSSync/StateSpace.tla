----------------------------- MODULE StateSpace -----------------------------
(*
The graph representation of n-ary ordered state space and 2D state space
used in CJupiter and XJupiter, respectively.  
*)
EXTENDS JupiterCtx, GraphsUtil
-----------------------------------------------------------------------------
IsSS(G) == \* A state space is a digraph with labeled edges.
    /\ IsGraph(G) \* It is a digraph (represented by a record).
    /\ G.node \subseteq (SUBSET Oid) \* Each node represents a document state, i.e., a set of Oid.
    /\ G.edge \subseteq [from: G.node, to: G.node, cop: Cop] \* Each edge is labeled with a Cop operation.

EmptySS == EmptyGraph
-----------------------------------------------------------------------------
Locate(cop, ss) == \* Locate the (unique) node in state space ss that matches the context of cop.     
    CHOOSE n \in ss.node : n = cop.ctx

\*RECURSIVE ExtractCopSeq(_, _, _, _) \* Extract a Cop sequence starting with u in ss at replica r.
\*ExtractCopSeq(NextEdge(_, _, _), r, u, ss) == 
\*    IF u = ds[r] THEN <<>>
\*    ELSE LET e == NextEdge(r, u, ss)
\*         IN  <<e.cop>> \o ExtractCopSeq(NextEdge, r, e.to, ss)
         
xForm(NextEdge(_, _, _), r, cop, ss) == \* Transform cop with an operation sequence 
    LET u == Locate(cop, ss)            \* in state space ss at replica r.
        v == u \cup {cop.oid}
        RECURSIVE xFormHelper(_, _, _, _)
        xFormHelper(uh, vh, coph, xss) == \* xss: eXtra ss created during transformation
            IF uh = ds[r] THEN [xcop |-> coph, 
                                xss |-> xss,
                                lss |-> [node |-> {vh}, 
                                         edge |-> {[from |-> uh, to |-> vh, cop |-> coph]}]]
            ELSE LET e == NextEdge(r, uh, ss)
                     copprime == e.cop
                     uprime == e.to
                     vprime == vh \cup {copprime.oid}
                     coph2copprime == COT(coph, copprime)
                     copprime2coph == COT(copprime, coph)
                 IN  xFormHelper(uprime, vprime, coph2copprime,
                        xss (+) [node |-> {vprime},
                                 edge |-> {[from |-> vh, to |-> vprime, cop |-> copprime2coph], 
                                           [from |-> uprime, to |-> vprime, cop |-> coph2copprime]}])
    IN  xFormHelper(u, v, cop, [node |-> {v}, edge |-> {[from |-> u, to |-> v, cop |-> cop]}])  

\*xFormCopCopsSS(cop, cops) == \* Transform cop against cops (a sequence of Cop) on state space.
\*    LET RECURSIVE xFormCopCopsSSHelper(_, _, _) 
\*        xFormCopCopsSSHelper(coph, copsh, xss) == 
\*            LET u == coph.ctx
\*                v == u \cup {coph.oid}
\*             uvSS == [node |-> {u, v}, edge |-> {[from |-> u, to |-> v, cop |-> coph]}]
\*             IN IF copsh = <<>> THEN [xcop |-> coph, xss |-> xss (+) uvSS, lss |-> uvSS]
\*                ELSE LET copprimeh == Head(copsh)
\*                            uprime == u \cup {copprimeh.oid}
\*                            vprime == u \cup {coph.oid, copprimeh.oid}
\*                         coph2copprimeh == COT(coph, copprimeh)
\*                         copprimeh2coph == COT(copprimeh, coph)
\*                      IN xFormCopCopsSSHelper(coph2copprimeh, Tail(copsh),
\*                            xss (+) [node |-> {u, v}, 
\*                                     edge |-> {[from |-> u, to |-> v, cop |-> coph],
\*                                               [from |-> u, to |-> uprime, cop |-> copprimeh],
\*                                               [from |-> v, to |-> vprime, cop |-> copprimeh2coph]}])
\*    IN  xFormCopCopsSSHelper(cop, cops, EmptySS)
\*
\*xFormSS(cop, copprime) == \* Transform cop against copprime on state space. 
\*    LET u == cop.ctx      \* Return the extra state space.
\*        v == u \cup {cop.oid}
\*        uprime == u \cup {copprime.oid}
\*        vprime == u \cup {cop.oid, copprime.oid}
\*        cop2copprime == COT(cop, copprime)
\*        copprime2cop == COT(copprime, cop)
\*    IN  [node |-> {u, v, uprime, vprime},
\*         edge |-> {[from |-> u, to |-> v, cop |-> cop],
\*                   [from |-> u, to |-> uprime, cop |-> copprime],
\*                   [from |-> v, to |-> vprime, cop |-> copprime2cop],
\*                   [from |-> uprime, to |-> vprime, cop |-> cop2copprime]}]
=============================================================================
\* Modification History
\* Last modified Wed Jan 09 15:31:43 CST 2019 by hengxin
\* Created Wed Dec 19 18:15:25 CST 2018 by hengxin