In GraphStateSpace:

\*RECURSIVE ExtractCopSeq(_, _, _, _) \* Extract a Cop sequence starting with u in ss at replica r.
\*ExtractCopSeq(NextEdge(_, _, _), r, u, ss) == 
\*    IF u = ds[r] THEN <<>>
\*    ELSE LET e == NextEdge(r, u, ss)
\*         IN  <<e.cop>> \o ExtractCopSeq(NextEdge, r, e.to, ss)
         
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


In BufferStateSpace:

RECURSIVE XformOpsOps(_, _,_) \* Transforms an operation sequence ops1 against another one ops2;
XformOpsOps(xform(_, _), ops1, ops2) == \* see Definition 2.13 of the paper "Imine@TCS06".
    IF ops2 = <<>>
    THEN ops1
    ELSE XformOpsOps(xform, XformOpsOp(xform, ops1, Head(ops2)), Tail(ops2))
