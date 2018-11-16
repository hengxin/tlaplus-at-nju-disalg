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
const_1542352209307165000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1542352209307166000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1542352209307167000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1542352209307169000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1542352209307170000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 15:10:09 CST 2018 by hengxin
