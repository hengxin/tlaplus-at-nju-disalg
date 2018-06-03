---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2, d3
----

\* MV CONSTANT definitions Data
const_15266340623452000 == 
{d1, d2, d3}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_15266340623453000 ==
/\ Len(AtoB) =< 3
/\ Len(BtoA) =< 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15266340623454000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15266340623455000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_15266340623456000 ==
ABS!FairSpec
----
=============================================================================
\* Modification History
\* Created Fri May 18 17:01:02 CST 2018 by hengxin
