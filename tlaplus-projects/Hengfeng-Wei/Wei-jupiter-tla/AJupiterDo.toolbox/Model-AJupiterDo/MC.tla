---- MODULE MC ----
EXTENDS AJupiterDo, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_153044927085110000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1State
const_153044927085211000 == 
<<"a", "b", "c">>
----

\* CONSTANT definitions @modelParameterConstants:2Cop
const_153044927085212000 == 
[c1 |-> <<Ins1>>, c2 |-> <<>>, c3 |-> <<>>]
----

\* CONSTANT definitions @modelParameterConstants:3Char
const_153044927085213000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:4Server
const_153044927085214000 == 
"s"
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153044927085215000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153044927085216000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sun Jul 01 20:47:50 CST 2018 by hengxin
