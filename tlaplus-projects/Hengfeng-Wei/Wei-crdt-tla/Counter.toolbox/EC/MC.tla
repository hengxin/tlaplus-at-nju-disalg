---- MODULE MC ----
EXTENDS Counter, TLC

\* CONSTANT definitions @modelParameterConstants:0Replica
const_152809153785475000 == 
{"r1", "r2", "r3", "r4"}
----

\* CONSTANT definitions @modelParameterConstants:1Max
const_152809153785476000 == 
[r1 |-> 1, r2 |-> 2, r3 |-> 3, r4 |-> 4]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_152809153785477000 ==
IncConstraint
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_152809153785478000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152809153785479000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_152809153785480000 ==
EC
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_152809153785481000 ==
SEC
----
=============================================================================
\* Modification History
\* Created Mon Jun 04 13:52:17 CST 2018 by hengxin
