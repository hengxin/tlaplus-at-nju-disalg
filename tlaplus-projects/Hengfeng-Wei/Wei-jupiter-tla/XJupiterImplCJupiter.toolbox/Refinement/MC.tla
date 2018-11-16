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
const_1542351255135135000 == 
{a}
----

\* MV CONSTANT definitions Client
const_1542351255135136000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_1542351255135137000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1542351255136139000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1542351255136140000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 14:54:15 CST 2018 by hengxin
