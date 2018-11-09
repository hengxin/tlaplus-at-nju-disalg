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
const_1541756814570144000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_1541756814570145000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_1541756814570146000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1541756814570148000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1541756814570149000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Fri Nov 09 17:46:54 CST 2018 by hengxin
