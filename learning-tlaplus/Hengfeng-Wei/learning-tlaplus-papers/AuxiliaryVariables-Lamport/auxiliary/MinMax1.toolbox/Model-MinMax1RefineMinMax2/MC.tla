---- MODULE MC ----
EXTENDS MinMax1, TLC

\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1540986261866218000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_1540986261866219000
----
\* CONSTANT definition @modelParameterDefinitions:4
def_ov_1540986261866220000 ==
1 .. 4
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540986261866221000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540986261866222000 ==
M!Spec
----
=============================================================================
\* Modification History
\* Created Wed Oct 31 19:44:21 CST 2018 by hengxin
