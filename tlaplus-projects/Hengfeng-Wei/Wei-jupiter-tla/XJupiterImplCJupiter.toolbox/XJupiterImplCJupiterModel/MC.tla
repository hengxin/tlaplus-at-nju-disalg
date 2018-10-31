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
const_1540983793892105000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1540983793892106000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1540983793892107000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540983793892109000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540983793892110000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Wed Oct 31 19:03:13 CST 2018 by hengxin
