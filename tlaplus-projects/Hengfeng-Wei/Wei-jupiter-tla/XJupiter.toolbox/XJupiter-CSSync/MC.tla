---- MODULE MC ----
EXTENDS XJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154234814715179000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154234814715180000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154234814715181000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154234814715183000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154234814715184000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 14:02:27 CST 2018 by hengxin
