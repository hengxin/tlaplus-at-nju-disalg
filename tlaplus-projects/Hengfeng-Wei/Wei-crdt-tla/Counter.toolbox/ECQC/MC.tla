---- MODULE MC ----
EXTENDS Counter, TLC

\* CONSTANT definitions @modelParameterConstants:0Replica
const_1530944770266203000 == 
{"r1", "r2"}
----

\* CONSTANT definitions @modelParameterConstants:1Max
const_1530944770266204000 == 
[r1 |-> 1, r2 |-> 2]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1530944770266205000 ==
IncConstraint
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530944770267206000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1530944770267207000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1530944770267208000 ==
EC
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1530944770267209000 ==
QC
----
=============================================================================
\* Modification History
\* Created Sat Jul 07 14:26:10 CST 2018 by hengxin
