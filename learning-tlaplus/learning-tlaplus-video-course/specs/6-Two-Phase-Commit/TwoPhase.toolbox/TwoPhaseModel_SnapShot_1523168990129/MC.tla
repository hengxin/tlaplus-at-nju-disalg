---- MODULE MC ----
EXTENDS TwoPhase, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3, r4, r5
----

\* MV CONSTANT definitions RM
const_152316898608134000 == 
{r1, r2, r3, r4, r5}
----

\* SYMMETRY definition
symm_152316898608135000 == 
Permutations(const_152316898608134000)
----

\* INIT definition @modelBehaviorInit:0
init_152316898608136000 ==
TPInit
----
\* NEXT definition @modelBehaviorNext:0
next_152316898608137000 ==
TPNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152316898608238000 ==
TPTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_152316898608239000 ==
TCConsistent
----
=============================================================================
\* Modification History
\* Created Sun Apr 08 14:29:46 CST 2018 by hengxin
