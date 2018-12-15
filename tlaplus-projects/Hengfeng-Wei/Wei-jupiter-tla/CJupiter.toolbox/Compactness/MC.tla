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
const_154486632271830000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154486632271831000 == 
{a, b}
----

\* SYMMETRY definition
symm_154486632271832000 == 
Permutations(const_154486632271831000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154486632271833000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154486632271835000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154486632271836000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Sat Dec 15 17:32:02 CST 2018 by hengxin
