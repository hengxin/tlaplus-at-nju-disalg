---- MODULE MC ----
EXTENDS TwoPhase, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3, r4, r5, r6, r7, r8, r9
----

\* MV CONSTANT definitions RM
const_15236093987767000 == 
{r1, r2, r3, r4, r5, r6, r7, r8, r9}
----

\* SYMMETRY definition
symm_15236093987768000 == 
Permutations(const_15236093987767000)
----

\* INIT definition @modelBehaviorInit:0
init_15236093987769000 ==
TPInit
----
\* NEXT definition @modelBehaviorNext:0
next_152360939877610000 ==
TPNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152360939877611000 ==
TPTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_152360939877612000 ==
TCConsistent
----
=============================================================================
\* Modification History
\* Created Fri Apr 13 16:49:58 CST 2018 by hengxin
