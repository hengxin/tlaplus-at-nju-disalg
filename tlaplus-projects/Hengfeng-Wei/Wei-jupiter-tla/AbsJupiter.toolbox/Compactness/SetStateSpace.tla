--------------------------- MODULE SetStateSpace ---------------------------
(*
Set representation of state space, used by AbsJupiter.
*)
EXTENDS JupiterCtx, JupiterSerial
-----------------------------------------------------------------------------
RECURSIVE xForm(_, _, _, _) \* Transform cop in state space ss at replica r \in Replica.
xForm(NextCop(_, _, _, _), r, cop, ss) == \* Return transformed cop and new state space ss after transformation.
    LET ctxDiff == ds[r] \ cop.ctx \* THEOREM: cop.ctx \subseteq ds[r]
        RECURSIVE xFormHelper(_, _, _)
        xFormHelper(coph, ctxDiffh, xss) == 
            IF ctxDiffh = {} THEN [xcop |-> coph, xss |-> xss]
            ELSE LET fcoph == NextCop(r, coph, ss, ctxDiffh)
                     xcoph == COT(coph, fcoph)
                    xfcoph == COT(fcoph, coph)
                 IN  xFormHelper(xcoph, ctxDiffh \ {fcoph.oid}, 
                                        xss \cup {xcoph, xfcoph})
    IN  xFormHelper(cop, ctxDiff, ss \cup {cop}) 

\*RECURSIVE xForm(_, _, _) \* Transform cop at replica r \in Replica.
\*xForm(r, cop, rcopss) == \* Return the transformed cop and the state space copss[r] after transformation.
\*    LET ctxDiff == ds[r] \ cop.ctx  \* THEOREM: cop.ctx \subseteq ds[r]
\*        RECURSIVE xFormHelper(_, _, _)
\*        xFormHelper(coph, ctxDiffh, copssr) == 
\*            IF ctxDiffh = {} THEN [xcop |-> coph, xcopss |-> copssr]
\*            ELSE LET foph == CHOOSE op \in ctxDiffh: \* the first op in serial
\*                                \A opprime \in ctxDiffh \ {op}: tb(op, opprime, serial[r])
\*                     fcophDict == {op \in copssr: op.oid = foph /\ op.ctx = coph.ctx}
\*                     fcoph == CHOOSE op \in fcophDict: TRUE \* THEOREM: Cardinality(fophDict) = 1
\*                     xcoph == COT(coph, fcoph)
\*                    xfcoph == COT(fcoph, coph)
\*                 IN  xFormHelper(xcoph, ctxDiffh \ {foph}, copssr \cup {xcoph, xfcoph})
\*    IN  xFormHelper(cop, ctxDiff, rcopss \cup {cop}) 
=============================================================================
\* Modification History
\* Last modified Thu Jan 10 08:24:51 CST 2019 by hengxin
\* Created Wed Jan 09 21:25:30 CST 2019 by hengxin