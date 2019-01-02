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
const_1546437875754234000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1546437875754235000 == 
{a, b}
----

\* SYMMETRY definition
symm_1546437875754236000 == 
Permutations(const_1546437875754235000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1546437875754237000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1546437875754238000 == 
AJMsgEx
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1546437875754240000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1546437875754241000 ==
XJ!Spec
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 22:04:35 CST 2019 by hengxin
