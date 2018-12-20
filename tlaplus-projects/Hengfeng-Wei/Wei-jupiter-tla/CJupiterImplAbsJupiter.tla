----------------------- MODULE CJupiterImplAbsJupiter -----------------------
(*
We show that CJupiter implements AbsJupiter.
*)
EXTENDS CJupiter
-----------------------------------------------------------------------------
AbsJ == INSTANCE AbsJupiter
            WITH copss <- [r \in Replica |-> {e.cop: e \in css[r].edge}]

THEOREM Spec => AbsJ!Spec
=============================================================================
\* Modification History
\* Last modified Tue Dec 18 22:44:49 CST 2018 by hengxin
\* Created Fri Dec 14 21:10:31 CST 2018 by hengxin