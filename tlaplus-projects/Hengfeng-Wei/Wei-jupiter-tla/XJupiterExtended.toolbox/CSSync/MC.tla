---- MODULE MC ----
EXTENDS XJupiterExtended, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1546434881611146000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1546434881611147000 == 
{a, b}
----

\* SYMMETRY definition
symm_1546434881611148000 == 
Permutations(const_1546434881611147000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1546434881611149000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1546434881611150000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1546434881612152000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1546434881612153000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 21:14:41 CST 2019 by hengxin
