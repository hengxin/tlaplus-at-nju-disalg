---- MODULE MC ----
EXTENDS WriteThroughCache, TLC

\* CONSTANT definitions @modelParameterConstants:0InitMemInt
const_1495613222234323000 == 
{0}
----

\* CONSTANT definitions @modelParameterConstants:1Adr
const_1495613222234324000 == 
{"a1", "a2", "a3"}
----

\* CONSTANT definitions @modelParameterConstants:2QLen
const_1495613222234325000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:3Val
const_1495613222234326000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:4Proc
const_1495613222234327000 == 
{"p1", "p2", "p3"}
----

\* CONSTANT definitions @modelParameterConstants:5Reply(p, d, miOld, miNew)
const_1495613222234328000(p, d, miOld, miNew) == 
/\ p \in Proc
/\ miOld \in InitMemInt
/\ miNew \in InitMemInt
/\ miNew = miOld
----

\* CONSTANT definitions @modelParameterConstants:6Send(p, d, miOld, miNew)
const_1495613222234329000(p, d, miOld, miNew) == 
/\ p \in Proc
/\ miOld \in InitMemInt
/\ miNew \in InitMemInt
/\ miNew = miOld
----

\* CONSTANT definition @modelParameterDefinitions:1
CONSTANT def_ov_1495613222234331000
----
\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1495613222234332000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_1495613222234333000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1495613222234334000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Wed May 24 16:07:02 CST 2017 by ics-ant
