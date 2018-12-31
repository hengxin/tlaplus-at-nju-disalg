---- MODULE MC ----
EXTENDS AJupiterImplXJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_15462569000992000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_15462569000993000 == 
{a, b}
----

\* SYMMETRY definition
symm_15462569000994000 == 
Permutations(const_15462569000993000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_15462569000995000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15462569001007000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_15462569001008000 ==
XJ!Spec
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 19:48:20 CST 2018 by hengxin
