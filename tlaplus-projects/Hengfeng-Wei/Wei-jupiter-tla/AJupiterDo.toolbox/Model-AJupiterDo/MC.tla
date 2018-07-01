---- MODULE MC ----
EXTENDS AJupiterDo, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_1530447891425106000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1State
const_1530447891425107000 == 
<<"a", "b", "c">>
----

\* CONSTANT definitions @modelParameterConstants:2Cop
const_1530447891425108000 == 
[c1 |-> <<Ins1>>, c2 |-> <<>>, c3 |-> <<>>]
----

\* CONSTANT definitions @modelParameterConstants:3Char
const_1530447891425109000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:4Server
const_1530447891425110000 == 
"s"
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530447891425111000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1530447891425112000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sun Jul 01 20:24:51 CST 2018 by hengxin
