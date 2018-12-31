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
const_154626095804023000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154626095804024000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154626095804025000 == 
Permutations(const_154626095804023000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154626095804026000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154626095804027000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154626095804028000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154626095804029000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 20:55:58 CST 2018 by hengxin
