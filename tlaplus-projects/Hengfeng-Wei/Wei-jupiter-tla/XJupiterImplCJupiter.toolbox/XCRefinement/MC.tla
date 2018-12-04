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
const_1543924055471179000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_1543924055471180000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_1543924055471181000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_1543924055471182000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1543924055471183000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1543924055471184000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Tue Dec 04 19:47:35 CST 2018 by hengxin
