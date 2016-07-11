---- MODULE MC ----
EXTENDS HSClock, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_146686175369739000 == 
20
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_146686175370740000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_146686175371741000 ==
ca \in [0 .. (N-1) -> {0, 1}]
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_146686175372742000 ==
CS!Spec
----
=============================================================================
\* Modification History
\* Created Sat Jun 25 21:35:53 CST 2016 by hengxin
