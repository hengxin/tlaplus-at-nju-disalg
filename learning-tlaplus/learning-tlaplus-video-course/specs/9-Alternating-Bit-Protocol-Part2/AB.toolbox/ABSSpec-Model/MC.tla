---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2, d3
----

\* MV CONSTANT definitions Data
const_1526131895942181000 == 
{d1, d2, d3}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1526131895942182000 ==
/\ Len(AtoB) =< 3
/\ Len(BtoA) =< 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1526131895942183000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1526131895942184000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1526131895942185000 ==
ABS!Spec
----
=============================================================================
\* Modification History
\* Created Sat May 12 21:31:35 CST 2018 by hengxin
