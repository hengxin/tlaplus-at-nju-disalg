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
const_1543929396909197000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_1543929396909198000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_1543929396909199000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_1543929396909200000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1543929396909201000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1543929396909202000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Tue Dec 04 21:16:36 CST 2018 by hengxin
