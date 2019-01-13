--------------------------- MODULE SetStateSpace ---------------------------
(*
Set representation of state space, used by AbsJupiter.
*)
EXTENDS JupiterCtx, JupiterSerial
-----------------------------------------------------------------------------
RECURSIVE xForm(_, _, _, _) \* Transform cop in state space ss at replica r \in Replica.
xForm(NextCop(_, _, _, _), r, cop, ss) == 
    LET ctxDiff == ds[r] \ cop.ctx \* THEOREM: cop.ctx \subseteq ds[r]
        RECURSIVE xFormHelper(_, _, _)
        xFormHelper(coph, ctxDiffh, xss) == \* Return transformed xcop 
            IF ctxDiffh = {} THEN [xcop |-> coph, xss |-> xss] \* and new state space xss 
            ELSE LET fcoph == NextCop(r, coph, ss, ctxDiffh)
                     xcoph == COT(coph, fcoph)
                    xfcoph == COT(fcoph, coph)
                 IN  xFormHelper(xcoph, ctxDiffh \ {fcoph.oid}, 
                                        xss \cup {xcoph, xfcoph})
    IN  xFormHelper(cop, ctxDiff, ss \cup {cop}) 
=============================================================================
\* Modification History
\* Last modified Thu Jan 10 08:55:58 CST 2019 by hengxin
\* Created Wed Jan 09 21:25:30 CST 2019 by hengxin