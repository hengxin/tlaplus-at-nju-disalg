---- MODULE MC ----
EXTENDS CJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_15456222278409000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154562222784010000 == 
{a, b}
----

\* SYMMETRY definition
symm_154562222784111000 == 
Permutations(const_154562222784010000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154562222784112000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154562222784114000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154562222784115000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Mon Dec 24 11:30:27 CST 2018 by hengxin
