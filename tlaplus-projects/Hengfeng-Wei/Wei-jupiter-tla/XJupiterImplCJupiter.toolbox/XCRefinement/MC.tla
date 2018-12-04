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
const_154384258331415000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154384258331416000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154384258331417000 == 
Permutations(const_154384258331415000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154384258331418000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154384258331419000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154384258331520000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154384258331521000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Mon Dec 03 21:09:43 CST 2018 by hengxin
