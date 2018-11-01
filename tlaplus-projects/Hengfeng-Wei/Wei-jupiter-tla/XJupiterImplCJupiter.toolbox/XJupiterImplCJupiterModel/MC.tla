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
const_154107353743224000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154107353743225000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154107353743226000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154107353743228000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154107353743329000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Thu Nov 01 19:58:57 CST 2018 by hengxin
