---- MODULE MC ----
EXTENDS AbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_15448658396179000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154486583961710000 == 
{a, b}
----

\* SYMMETRY definition
symm_154486583961711000 == 
Permutations(const_154486583961710000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154486583961712000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154486583961714000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154486583961715000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Sat Dec 15 17:23:59 CST 2018 by hengxin
