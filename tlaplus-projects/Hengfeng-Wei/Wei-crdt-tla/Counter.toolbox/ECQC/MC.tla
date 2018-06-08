---- MODULE MC ----
EXTENDS Counter, TLC

\* CONSTANT definitions @modelParameterConstants:0Replica
const_152844656619965000 == 
{"r1", "r2", "r3", "r4"}
----

\* CONSTANT definitions @modelParameterConstants:1Max
const_152844656620066000 == 
[r1 |-> 1, r2 |-> 2, r3 |-> 3, r4 |-> 4]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_152844656620067000 ==
IncConstraint
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_152844656620068000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152844656620069000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_152844656620070000 ==
EC
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_152844656620071000 ==
QC
----
=============================================================================
\* Modification History
\* Created Fri Jun 08 16:29:26 CST 2018 by hengxin
