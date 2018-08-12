---- MODULE MC ----
EXTENDS ABSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0Data
const_1533997384847220000 == 
{"a", "b", "c"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1533997384847221000 ==
FairSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1533997384847222000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1533997384847223000 ==
Inv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1533997384847224000 ==
FairSpec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1533997384847225000 ==
DeliveryLiveness
----
=============================================================================
\* Modification History
\* Created Sat Aug 11 22:23:04 CST 2018 by hengxin
