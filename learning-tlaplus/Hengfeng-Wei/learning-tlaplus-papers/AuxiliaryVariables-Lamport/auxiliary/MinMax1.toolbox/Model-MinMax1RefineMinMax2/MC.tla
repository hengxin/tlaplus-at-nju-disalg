---- MODULE MC ----
EXTENDS MinMax1, TLC

\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1530018908579148000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_1530018908579149000
----
\* CONSTANT definition @modelParameterDefinitions:4
def_ov_1530018908579150000 ==
1 .. 20
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530018908579151000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1530018908579152000 ==
M!Spec
----
=============================================================================
\* Modification History
\* Created Tue Jun 26 21:15:08 CST 2018 by hengxin
