---- MODULE MC ----
EXTENDS XJupiterImplCJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1
----

\* MV CONSTANT definitions Char
const_154461878355462000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154461878355463000 == 
{c1}
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154461878355464000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154461878355565000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154461878355566000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154461878355567000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Wed Dec 12 20:46:23 CST 2018 by hengxin
