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
const_15423438738672000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_15423438738673000 == 
{c1}
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_15423438738674000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15423438738676000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_15423438738677000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 12:51:13 CST 2018 by hengxin
