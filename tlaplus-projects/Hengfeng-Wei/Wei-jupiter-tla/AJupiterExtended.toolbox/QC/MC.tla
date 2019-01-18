---- MODULE MC ----
EXTENDS AJupiterExtended, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154769275425810000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154769275425811000 == 
{a, b}
----

\* SYMMETRY definition
symm_154769275425812000 == 
Permutations(const_154769275425811000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154769275425813000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154769275425814000 == 
AJMsgEx
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154769275425816000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154769275425817000 ==
QC
----
=============================================================================
\* Modification History
\* Created Thu Jan 17 10:39:14 CST 2019 by hengxin
