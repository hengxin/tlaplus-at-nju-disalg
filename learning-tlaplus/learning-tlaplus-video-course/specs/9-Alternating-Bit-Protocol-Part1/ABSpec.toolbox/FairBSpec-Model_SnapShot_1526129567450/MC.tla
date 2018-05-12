---- MODULE MC ----
EXTENDS ABSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f, g
----

\* MV CONSTANT definitions Data
const_1526129563422127000 == 
{a, b, c, d, e, f, g}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1526129563422128000 ==
FairBSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1526129563422129000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1526129563422130000 ==
Inv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1526129563422131000 ==
\A v \in Data \X {0,1} : (AVar = v) ~> (BVar = v)
----
=============================================================================
\* Modification History
\* Created Sat May 12 20:52:43 CST 2018 by hengxin
