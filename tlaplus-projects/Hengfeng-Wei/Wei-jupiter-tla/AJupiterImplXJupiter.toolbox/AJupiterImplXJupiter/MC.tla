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
const_154769337412818000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154769337412819000 == 
{a, b}
----

\* SYMMETRY definition
symm_154769337412820000 == 
Permutations(const_154769337412819000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154769337412821000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154769337412822000 == 
AJMsgEx
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154769337412824000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154769337412825000 ==
XJ!Spec
----
=============================================================================
\* Modification History
\* Created Thu Jan 17 10:49:34 CST 2019 by hengxin
