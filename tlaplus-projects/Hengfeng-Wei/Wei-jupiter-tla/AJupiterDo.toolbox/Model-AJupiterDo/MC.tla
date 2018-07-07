---- MODULE MC ----
EXTENDS AJupiterDo, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_1530893211135161000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1State
const_1530893211135162000 == 
<<"a", "b", "c">>
----

\* CONSTANT definitions @modelParameterConstants:2Cop
const_1530893211135163000 == 
[c1 |-> <<Ins1>>, c2 |-> <<>>, c3 |-> <<>>]
----

\* CONSTANT definitions @modelParameterConstants:3Char
const_1530893211135164000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:4Server
const_1530893211135165000 == 
"s"
----

\* CONSTANT definitions @modelParameterConstants:5MaxPos
const_1530893211135166000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:6MaxPr
const_1530893211135167000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:7MaxLen
const_1530893211135168000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530893211136170000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1530893211136171000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sat Jul 07 00:06:51 CST 2018 by hengxin
