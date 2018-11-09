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
const_154159477818390000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154159477818391000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154159477818392000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154159477818394000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154159477818395000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Wed Nov 07 20:46:18 CST 2018 by hengxin
