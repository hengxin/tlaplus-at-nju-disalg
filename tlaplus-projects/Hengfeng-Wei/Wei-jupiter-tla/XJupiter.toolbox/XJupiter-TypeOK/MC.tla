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
const_153915481149929000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_153915481149930000 == 
{a, b}
----

\* SYMMETRY definition
symm_153915481149931000 == 
Permutations(const_153915481149929000) \union Permutations(const_153915481149930000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_153915481149932000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153915481149934000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153915481149935000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Wed Oct 10 15:00:11 CST 2018 by hengxin
