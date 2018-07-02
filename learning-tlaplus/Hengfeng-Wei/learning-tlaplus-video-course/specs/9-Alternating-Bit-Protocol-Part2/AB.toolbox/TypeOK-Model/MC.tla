---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2, d3
----

\* MV CONSTANT definitions Data
const_1526131667708172000 == 
{d1, d2, d3}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1526131667708173000 ==
/\ Len(AtoB) =< 3
/\ Len(BtoA) =< 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1526131667708174000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1526131667708175000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sat May 12 21:27:47 CST 2018 by hengxin
