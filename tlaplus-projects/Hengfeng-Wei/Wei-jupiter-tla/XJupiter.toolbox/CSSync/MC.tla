---- MODULE MC ----
EXTENDS XJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_15462604381139000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154626043811310000 == 
{a, b}
----

\* SYMMETRY definition
symm_154626043811311000 == 
Permutations(const_154626043811310000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154626043811312000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154626043811414000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154626043811415000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 20:47:18 CST 2018 by hengxin
