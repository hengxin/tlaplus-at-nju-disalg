---- MODULE MC ----
EXTENDS XJupiterImplCJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Char
const_154234885621897000 == 
{a}
----

\* MV CONSTANT definitions Client
const_154234885621898000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154234885621899000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1542348856219101000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1542348856219102000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 14:14:16 CST 2018 by hengxin
