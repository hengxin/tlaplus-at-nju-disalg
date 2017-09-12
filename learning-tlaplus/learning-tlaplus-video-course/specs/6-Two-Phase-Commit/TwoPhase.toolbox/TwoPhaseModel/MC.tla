---- MODULE MC ----
EXTENDS TwoPhase, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3, r4, r5
----

\* MV CONSTANT definitions RM
const_1505213861633124000 == 
{r1, r2, r3, r4, r5}
----

\* SYMMETRY definition
symm_1505213861633125000 == 
Permutations(const_1505213861633124000)
----

\* INIT definition @modelBehaviorInit:0
init_1505213861633126000 ==
TPInit
----
\* NEXT definition @modelBehaviorNext:0
next_1505213861633127000 ==
TPNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1505213861633128000 ==
TPTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1505213861633129000 ==
TCConsistent
----
=============================================================================
\* Modification History
\* Created Tue Sep 12 18:57:41 CST 2017 by hengxin
