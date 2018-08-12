---- MODULE MC ----
EXTENDS AB, TLC

\* CONSTANT definitions @modelParameterConstants:0Data
const_1534044764479236000 == 
{"d1", "d2"}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1534044764479237000 ==
/\ Len(AtoB) =< 3
/\ Len(BtoA) =< 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534044764479238000 ==
FairSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534044764479239000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1534044764479240000 ==
ABS!FairSpec
----
=============================================================================
\* Modification History
\* Created Sun Aug 12 11:32:44 CST 2018 by hengxin
