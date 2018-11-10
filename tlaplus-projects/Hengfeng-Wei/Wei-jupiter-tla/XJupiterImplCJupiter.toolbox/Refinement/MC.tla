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
const_15418606536138000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_15418606536139000 == 
{c1}
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154186065361310000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154186065361312000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154186065361413000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Sat Nov 10 22:37:33 CST 2018 by hengxin
