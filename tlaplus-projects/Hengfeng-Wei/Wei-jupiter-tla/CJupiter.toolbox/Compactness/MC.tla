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
const_15462598047882000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_15462598047883000 == 
{a, b}
----

\* SYMMETRY definition
symm_15462598047884000 == 
Permutations(const_15462598047883000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_15462598047885000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15462598047897000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15462598047898000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 20:36:44 CST 2018 by hengxin
