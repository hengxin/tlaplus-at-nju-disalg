----------------------- MODULE CJupiterImplAbsJupiter -----------------------
EXTENDS CJupiter
-----------------------------------------------------------------------------
AbsJ == INSTANCE AbsJupiter
            WITH copss <- [r \in Replica |-> {e.cop: e \in css[r].edge}]

THEOREM Spec => AbsJ!Spec
=============================================================================
\* Modification History
\* Last modified Wed Jan 02 21:04:52 CST 2019 by hengxin
\* Created Fri Dec 14 21:10:31 CST 2018 by hengxin