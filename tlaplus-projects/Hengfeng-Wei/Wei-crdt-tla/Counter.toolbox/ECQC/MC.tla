---- MODULE MC ----
EXTENDS Counter, TLC

\* CONSTANT definitions @modelParameterConstants:0Replica
const_153389401845488000 == 
{"r1", "r2"}
----

\* CONSTANT definitions @modelParameterConstants:1Max
const_153389401845489000 == 
[r1 |-> 0, r2 |-> 1]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_153389401845490000 ==
IncConstraint
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153389401845491000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153389401845492000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_153389401845493000 ==
EC
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_153389401845494000 ==
QC
----
=============================================================================
\* Modification History
\* Created Fri Aug 10 17:40:18 CST 2018 by hengxin
