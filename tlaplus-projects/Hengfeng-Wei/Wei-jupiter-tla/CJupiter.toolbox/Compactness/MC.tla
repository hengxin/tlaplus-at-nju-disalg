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
const_15462251297539000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154622512975310000 == 
{a, b}
----

\* SYMMETRY definition
symm_154622512975311000 == 
Permutations(const_154622512975310000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154622512975312000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154622512975314000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154622512975315000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 10:58:49 CST 2018 by hengxin
