---- MODULE MC ----
EXTENDS TwoPhase, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3, r4, r5, r6, r7, r8, r9, r10
----

\* MV CONSTANT definitions RM
const_152316902468852000 == 
{r1, r2, r3, r4, r5, r6, r7, r8, r9, r10}
----

\* SYMMETRY definition
symm_152316902468853000 == 
Permutations(const_152316902468852000)
----

\* INIT definition @modelBehaviorInit:0
init_152316902468854000 ==
TPInit
----
\* NEXT definition @modelBehaviorNext:0
next_152316902468855000 ==
TPNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152316902468856000 ==
TPTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_152316902468857000 ==
TCConsistent
----
=============================================================================
\* Modification History
\* Created Sun Apr 08 14:30:24 CST 2018 by hengxin
