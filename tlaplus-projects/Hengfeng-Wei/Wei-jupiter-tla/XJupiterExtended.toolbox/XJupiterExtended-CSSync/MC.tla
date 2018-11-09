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
const_1541756595967132000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1541756595967133000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1541756595967134000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1541756595967136000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1541756595967137000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Fri Nov 09 17:43:15 CST 2018 by hengxin
