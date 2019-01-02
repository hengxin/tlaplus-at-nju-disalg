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
const_1546437175383202000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1546437175383203000 == 
{a, b}
----

\* SYMMETRY definition
symm_1546437175383204000 == 
Permutations(const_1546437175383203000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1546437175383205000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1546437175383206000 == 
AJMsgEx
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1546437175383208000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1546437175383209000 ==
TypeOKEx
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 21:52:55 CST 2019 by hengxin
