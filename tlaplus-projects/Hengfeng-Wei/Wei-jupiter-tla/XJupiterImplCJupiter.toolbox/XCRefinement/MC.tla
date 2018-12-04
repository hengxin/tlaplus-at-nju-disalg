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
const_1543929673973203000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_1543929673973204000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_1543929673973205000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_1543929673973206000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1543929673973207000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1543929673973208000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Tue Dec 04 21:21:13 CST 2018 by hengxin
