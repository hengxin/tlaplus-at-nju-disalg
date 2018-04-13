---- MODULE MC ----
EXTENDS JupiterOT, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e
----

\* MV CONSTANT definitions CH
const_15054686381596000 == 
{a, b, c, d, e}
----

\* SYMMETRY definition
symm_15054686381607000 == 
Permutations(const_15054686381596000)
----

\* CONSTANT definitions @modelParameterConstants:1NODE
const_15054686381608000 == 
{0,1}
----

\* INIT definition @modelBehaviorInit:0
init_15054686381609000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_150546863816010000 ==
Next
----
=============================================================================
\* Modification History
\* Created Fri Sep 15 17:43:58 CST 2017 by hengxin
