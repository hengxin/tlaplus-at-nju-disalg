---- MODULE MC ----
EXTENDS AB, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2, d3
----

\* MV CONSTANT definitions Data
const_1526131632441165000 == 
{d1, d2, d3}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1526131632441166000 ==
/\ Len(AtoB) =< 3
/\ Len(BtoA) =< 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1526131632441167000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Sat May 12 21:27:12 CST 2018 by hengxin
