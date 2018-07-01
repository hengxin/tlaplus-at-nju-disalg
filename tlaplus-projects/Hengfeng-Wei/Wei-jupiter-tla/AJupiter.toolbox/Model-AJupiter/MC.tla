---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_153045137599519000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1State
const_153045137599620000 == 
<<"a", "b", "c">>
----

\* CONSTANT definitions @modelParameterConstants:2Cop
const_153045137599621000 == 
[c1 |-> <<Ins1>>, c2 |-> <<>>, c3 |-> <<>>]
----

\* CONSTANT definitions @modelParameterConstants:3Char
const_153045137599622000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:4Server
const_153045137599623000 == 
"s"
----

\* CONSTANT definition @modelParameterDefinitions:1
CONSTANT def_ov_153045137599625000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153045137599626000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153045137599627000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sun Jul 01 21:22:55 CST 2018 by hengxin
