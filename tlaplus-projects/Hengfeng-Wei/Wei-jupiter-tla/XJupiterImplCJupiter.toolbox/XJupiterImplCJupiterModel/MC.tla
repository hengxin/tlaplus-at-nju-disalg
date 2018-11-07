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
const_154156196996344000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154156196996345000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154156196996346000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154156196996348000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154156196996349000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Wed Nov 07 11:39:29 CST 2018 by hengxin
