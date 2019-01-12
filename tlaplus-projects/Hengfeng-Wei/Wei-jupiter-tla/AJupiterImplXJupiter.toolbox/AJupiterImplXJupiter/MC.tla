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
const_1547298595430122000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1547298595430123000 == 
{a, b}
----

\* SYMMETRY definition
symm_1547298595430124000 == 
Permutations(const_1547298595430123000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1547298595430125000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1547298595430126000 == 
AJMsgEx
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1547298595430128000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1547298595430129000 ==
XJ!Spec
----
=============================================================================
\* Modification History
\* Created Sat Jan 12 21:09:55 CST 2019 by hengxin
