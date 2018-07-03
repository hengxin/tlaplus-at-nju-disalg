---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_153060115322247000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1State
const_153060115322248000 == 
<<"a", "b", "c">>
----

\* CONSTANT definitions @modelParameterConstants:2Cop
const_153060115322249000 == 
[c1 |-> <<Ins1>>, c2 |-> <<>>, c3 |-> <<>>]
----

\* CONSTANT definitions @modelParameterConstants:3Char
const_153060115322250000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:4Server
const_153060115322251000 == 
"s"
----

\* CONSTANT definition @modelParameterDefinitions:1
CONSTANT def_ov_153060115322253000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153060115322254000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153060115322255000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Tue Jul 03 14:59:13 CST 2018 by hengxin
