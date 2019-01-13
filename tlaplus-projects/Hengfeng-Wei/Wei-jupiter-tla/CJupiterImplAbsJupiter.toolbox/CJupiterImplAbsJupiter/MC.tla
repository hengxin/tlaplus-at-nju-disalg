---- MODULE MC ----
EXTENDS CJupiterImplAbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Char
const_154734575616110000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154734575616111000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154734575616112000 == 
Permutations(const_154734575616110000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154734575616113000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154734575616114000 == 
Cop
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154734575616115000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154734575616116000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154734575616117000 ==
AbsJ!Spec
----
=============================================================================
\* Modification History
\* Created Sun Jan 13 10:15:56 CST 2019 by hengxin
