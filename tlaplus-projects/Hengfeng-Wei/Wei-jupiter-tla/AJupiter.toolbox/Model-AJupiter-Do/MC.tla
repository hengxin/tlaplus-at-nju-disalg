---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_1530950599897141000 == 
{"c1", "c2", "c3", "c4"}
----

\* CONSTANT definitions @modelParameterConstants:1Cop
const_1530950599897142000 == 
[c1 |-> <<Ins1>>, c2 |-> <<Ins1>>, c3 |-> <<Del1>>, c4 |-> <<Ins2>>]
----

\* CONSTANT definitions @modelParameterConstants:2Char
const_1530950599897143000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:3Server
const_1530950599897144000 == 
"s"
----

\* CONSTANT definitions @modelParameterConstants:4InitState
const_1530950599897145000 == 
<<"a", "b">>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530950599897147000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1530950599897148000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1530950599897149000 ==
QC
----
=============================================================================
\* Modification History
\* Created Sat Jul 07 16:03:19 CST 2018 by hengxin
