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
const_154693155607710000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154693155607711000 == 
{a, b}
----

\* SYMMETRY definition
symm_154693155607712000 == 
Permutations(const_154693155607711000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154693155607713000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154693155607714000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154693155607816000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154693155607817000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Tue Jan 08 15:12:36 CST 2019 by hengxin
