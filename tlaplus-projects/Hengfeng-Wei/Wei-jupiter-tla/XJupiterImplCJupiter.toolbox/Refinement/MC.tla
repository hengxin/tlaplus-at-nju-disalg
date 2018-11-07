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
const_154157774634978000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154157774634979000 == 
{c1, c2}
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154157774635180000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154157774635182000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154157774635183000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Wed Nov 07 16:02:26 CST 2018 by hengxin
