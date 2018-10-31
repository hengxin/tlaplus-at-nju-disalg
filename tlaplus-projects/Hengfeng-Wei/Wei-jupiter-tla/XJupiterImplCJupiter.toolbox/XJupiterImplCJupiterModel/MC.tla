---- MODULE MC ----
EXTENDS XJupiterImplCJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154097816721470000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154097816721471000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154097816721472000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154097816721474000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154097816721475000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Wed Oct 31 17:29:27 CST 2018 by hengxin
