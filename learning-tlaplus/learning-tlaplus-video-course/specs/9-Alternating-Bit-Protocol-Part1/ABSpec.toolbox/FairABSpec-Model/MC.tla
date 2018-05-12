---- MODULE MC ----
EXTENDS ABSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f, g
----

\* MV CONSTANT definitions Data
const_1526131952150216000 == 
{a, b, c, d, e, f, g}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1526131952150217000 ==
FairSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1526131952150218000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1526131952150219000 ==
Inv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1526131952150220000 ==
\A v \in Data \X {0,1} : (AVar = v) ~> (BVar = v)
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1526131952150221000 ==
FairABSpec
----
=============================================================================
\* Modification History
\* Created Sat May 12 21:32:32 CST 2018 by hengxin
