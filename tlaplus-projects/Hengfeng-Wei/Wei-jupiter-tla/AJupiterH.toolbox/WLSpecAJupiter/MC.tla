---- MODULE MC ----
EXTENDS AJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1543920491206124000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1543920491206125000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1543920491206126000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1543920491206128000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1543920491206129000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Tue Dec 04 18:48:11 CST 2018 by hengxin
