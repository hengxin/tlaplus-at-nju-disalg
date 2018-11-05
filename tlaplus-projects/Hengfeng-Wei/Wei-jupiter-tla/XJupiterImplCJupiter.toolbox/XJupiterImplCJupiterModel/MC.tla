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
const_154139990274426000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154139990274427000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154139990274428000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154139990274430000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154139990274431000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Mon Nov 05 14:38:22 CST 2018 by hengxin
