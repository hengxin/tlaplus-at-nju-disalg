---- MODULE MC ----
EXTENDS MinMax2H, TLC

\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1530020117537182000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_1530020117537183000
----
\* CONSTANT definition @modelParameterDefinitions:4
CONSTANT def_ov_1530020117537184000
----
\* CONSTANT definition @modelParameterDefinitions:5
CONSTANT def_ov_1530020117537185000
----
\* CONSTANT definition @modelParameterDefinitions:6
def_ov_1530020117537186000 ==
1 .. 20
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530020117537187000 ==
SpecH
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1530020117537188000 ==
M!Spec
----
=============================================================================
\* Modification History
\* Created Tue Jun 26 21:35:17 CST 2018 by hengxin
