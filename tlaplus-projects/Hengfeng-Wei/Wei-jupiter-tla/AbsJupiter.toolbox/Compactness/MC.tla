---- MODULE MC ----
EXTENDS AbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_154444647905749000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154444647905850000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_154444647905851000 == 
Permutations(const_154444647905850000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154444647905852000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154444647905854000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154444647905855000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Mon Dec 10 20:54:39 CST 2018 by hengxin
