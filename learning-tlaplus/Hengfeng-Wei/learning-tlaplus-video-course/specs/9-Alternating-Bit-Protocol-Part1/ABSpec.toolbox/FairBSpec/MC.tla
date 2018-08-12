---- MODULE MC ----
EXTENDS ABSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0Data
const_1533997180097197000 == 
{"a", "b", "c"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1533997180097198000 ==
FairBSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1533997180097199000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1533997180097200000 ==
Inv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1533997180097201000 ==
DeliveryLiveness
----
=============================================================================
\* Modification History
\* Created Sat Aug 11 22:19:40 CST 2018 by hengxin
