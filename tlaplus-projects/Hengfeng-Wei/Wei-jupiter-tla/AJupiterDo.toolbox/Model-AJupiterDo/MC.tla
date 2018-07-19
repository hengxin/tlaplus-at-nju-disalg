---- MODULE MC ----
EXTENDS AJupiterDo, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_1530944468431153000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1Cop
const_1530944468431154000 == 
[c1 |-> <<Ins1>>, c2 |-> <<>>, c3 |-> <<>>]
----

\* CONSTANT definitions @modelParameterConstants:2Char
const_1530944468431155000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:3Server
const_1530944468431156000 == 
"s"
----

\* CONSTANT definitions @modelParameterConstants:4InitState
const_1530944468431157000 == 
<<"a", "b">>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530944468431159000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1530944468431160000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sat Jul 07 14:21:08 CST 2018 by hengxin
