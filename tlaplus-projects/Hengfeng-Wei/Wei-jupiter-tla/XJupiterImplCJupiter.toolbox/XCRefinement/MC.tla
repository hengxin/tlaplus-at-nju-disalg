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
const_154521677113437000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154521677113438000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154521677113439000 == 
Permutations(const_154521677113437000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154521677113440000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154521677113441000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154521677113442000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154521677113443000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Wed Dec 19 18:52:51 CST 2018 by hengxin
