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
const_154707989936126000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154707989936127000 == 
{a, b}
----

\* SYMMETRY definition
symm_154707989936128000 == 
Permutations(const_154707989936127000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154707989936129000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154707989936130000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154707989936132000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154707989936133000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Thu Jan 10 08:24:59 CST 2019 by hengxin
