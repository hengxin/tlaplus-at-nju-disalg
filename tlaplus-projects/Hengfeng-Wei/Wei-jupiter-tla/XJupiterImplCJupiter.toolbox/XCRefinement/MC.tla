---- MODULE MC ----
EXTENDS XJupiterImplCJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Char
const_154734593179618000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154734593179619000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154734593179620000 == 
Permutations(const_154734593179618000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154734593179621000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154734593179622000 == 
Cop
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154734593179623000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154734593179624000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154734593179725000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Sun Jan 13 10:18:51 CST 2019 by hengxin
