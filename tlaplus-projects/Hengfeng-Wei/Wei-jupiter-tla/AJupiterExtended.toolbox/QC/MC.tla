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
const_1546436914866194000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1546436914866195000 == 
{a, b}
----

\* SYMMETRY definition
symm_1546436914866196000 == 
Permutations(const_1546436914866195000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1546436914866197000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1546436914866198000 == 
AJMsgEx
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1546436914866200000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1546436914866201000 ==
QC
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 21:48:34 CST 2019 by hengxin
