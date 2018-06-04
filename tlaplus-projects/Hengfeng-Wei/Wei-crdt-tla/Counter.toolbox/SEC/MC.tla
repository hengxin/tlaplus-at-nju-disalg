---- MODULE MC ----
EXTENDS Counter, TLC

\* CONSTANT definitions @modelParameterConstants:0Replica
const_152811322951044000 == 
{"r1", "r2", "r3", "r4"}
----

\* CONSTANT definitions @modelParameterConstants:1Max
const_152811322951145000 == 
[r1 |-> 1, r2 |-> 2, r3 |-> 3, r4 |-> 4]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_152811322951146000 ==
IncConstraint
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_152811322951147000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152811322951148000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_152811322951149000 ==
EC
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_152811322951150000 ==
SEC
----
=============================================================================
\* Modification History
\* Created Mon Jun 04 19:53:49 CST 2018 by hengxin
