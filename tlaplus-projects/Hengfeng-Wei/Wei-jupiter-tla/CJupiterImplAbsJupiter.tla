----------------------- MODULE CJupiterImplAbsJupiter -----------------------
(*
We show that CJupiter implements AbsJupiter.
*)
EXTENDS CJupiter
-----------------------------------------------------------------------------
AbsJ == INSTANCE AbsJupiter
            WITH ds <- cur,
                 copss <- [r \in Replica |-> {e.cop: e \in css[r].edge}]

THEOREM Spec => AbsJ!Spec
=============================================================================
\* Modification History
\* Last modified Fri Dec 14 21:26:52 CST 2018 by hengxin
\* Created Fri Dec 14 21:10:31 CST 2018 by hengxin