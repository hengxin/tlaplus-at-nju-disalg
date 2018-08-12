---- MODULE MC ----
EXTENDS ABSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0Data
const_1533997128079187000 == 
{"a", "b", "c"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1533997128079188000 ==
FairSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1533997128079189000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1533997128079190000 ==
Inv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1533997128079191000 ==
DeliveryLiveness
----
=============================================================================
\* Modification History
\* Created Sat Aug 11 22:18:48 CST 2018 by hengxin
