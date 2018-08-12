---- MODULE MC ----
EXTENDS AB, TLC

\* CONSTANT definitions @modelParameterConstants:0Data
const_1534045055629258000 == 
{"d1", "d2"}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1534045055629259000 ==
/\ Len(AtoB) =< 3
/\ Len(BtoA) =< 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534045055629260000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534045055629261000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1534045055629262000 ==
ABS!Spec
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1534045055629263000 ==
ABS!FairSpec
----
=============================================================================
\* Modification History
\* Created Sun Aug 12 11:37:35 CST 2018 by hengxin
