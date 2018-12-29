---- MODULE MC ----
EXTENDS AJupiterExtended, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154607662266937000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154607662266938000 == 
{a, b}
----

\* SYMMETRY definition
symm_154607662266939000 == 
Permutations(const_154607662266938000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154607662266940000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154607662266942000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154607662266943000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sat Dec 29 17:43:42 CST 2018 by hengxin
