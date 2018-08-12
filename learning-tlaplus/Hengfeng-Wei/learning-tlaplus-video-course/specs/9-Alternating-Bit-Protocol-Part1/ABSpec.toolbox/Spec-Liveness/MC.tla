---- MODULE MC ----
EXTENDS ABSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0Data
const_1533997027991177000 == 
{"a", "b"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1533997027991178000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1533997027991179000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1533997027991180000 ==
Inv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1533997027991181000 ==
DeliveryLiveness
----
=============================================================================
\* Modification History
\* Created Sat Aug 11 22:17:07 CST 2018 by hengxin
