---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_1530968776529213000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1Cop
const_1530968776529214000 == 
[c1 |-> <<Ins1>>, c2 |-> <<Ins2, Ins3>>, c3 |-> <<Del3>>]
----

\* CONSTANT definitions @modelParameterConstants:2Char
const_1530968776529215000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:3Server
const_1530968776529216000 == 
"s"
----

\* CONSTANT definitions @modelParameterConstants:4InitState
const_1530968776529217000 == 
<<"a", "b">>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530968776529219000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1530968776529220000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1530968776529221000 ==
QC
----
=============================================================================
\* Modification History
\* Created Sat Jul 07 21:06:16 CST 2018 by hengxin
