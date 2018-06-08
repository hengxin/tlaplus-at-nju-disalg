---- MODULE MC ----
EXTENDS Counter, TLC

\* CONSTANT definitions @modelParameterConstants:0Replica
const_152842846228958000 == 
{"r1", "r2", "r3", "r4"}
----

\* CONSTANT definitions @modelParameterConstants:1Max
const_152842846228959000 == 
[r1 |-> 1, r2 |-> 2, r3 |-> 3, r4 |-> 4]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_152842846228960000 ==
IncConstraint
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_152842846228961000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152842846229162000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_152842846229163000 ==
EC
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_152842846229164000 ==
QC
----
=============================================================================
\* Modification History
\* Created Fri Jun 08 11:27:42 CST 2018 by hengxin
