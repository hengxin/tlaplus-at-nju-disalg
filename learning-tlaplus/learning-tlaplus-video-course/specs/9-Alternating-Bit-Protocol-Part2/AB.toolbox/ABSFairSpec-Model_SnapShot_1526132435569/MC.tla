---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2, d3
----

\* MV CONSTANT definitions Data
const_1526132433540227000 == 
{d1, d2, d3}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1526132433540228000 ==
/\ Len(AtoB) =< 3
/\ Len(BtoA) =< 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1526132433540229000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1526132433540230000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1526132433540231000 ==
ABS!FairSpec
----
=============================================================================
\* Modification History
\* Created Sat May 12 21:40:33 CST 2018 by hengxin
