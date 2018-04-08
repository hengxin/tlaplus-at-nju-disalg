---- MODULE MC ----
EXTENDS TwoPhase, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3, r4, r5, r6, r7, r8, r9
----

\* MV CONSTANT definitions RM
const_152316918285276000 == 
{r1, r2, r3, r4, r5, r6, r7, r8, r9}
----

\* SYMMETRY definition
symm_152316918285277000 == 
Permutations(const_152316918285276000)
----

\* INIT definition @modelBehaviorInit:0
init_152316918285278000 ==
TPInit
----
\* NEXT definition @modelBehaviorNext:0
next_152316918285279000 ==
TPNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152316918285280000 ==
TPTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_152316918285281000 ==
TCConsistent
----
=============================================================================
\* Modification History
\* Created Sun Apr 08 14:33:02 CST 2018 by hengxin
