---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2, d3
----

\* MV CONSTANT definitions Data
const_1526132459859237000 == 
{d1, d2, d3}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1526132459859238000 ==
/\ Len(AtoB) =< 3
/\ Len(BtoA) =< 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1526132459859239000 ==
FairSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1526132459859240000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1526132459859241000 ==
ABS!FairSpec
----
=============================================================================
\* Modification History
\* Created Sat May 12 21:40:59 CST 2018 by hengxin
