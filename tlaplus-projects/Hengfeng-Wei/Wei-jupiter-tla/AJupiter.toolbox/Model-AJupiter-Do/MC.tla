---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_153045174139246000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1State
const_153045174139247000 == 
<<"a", "b", "c">>
----

\* CONSTANT definitions @modelParameterConstants:2Cop
const_153045174139248000 == 
[c1 |-> <<Ins1>>, c2 |-> <<>>, c3 |-> <<>>]
----

\* CONSTANT definitions @modelParameterConstants:3Char
const_153045174139249000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:4Server
const_153045174139250000 == 
"s"
----

\* CONSTANT definition @modelParameterDefinitions:1
CONSTANT def_ov_153045174139252000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153045174139253000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153045174139254000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sun Jul 01 21:29:01 CST 2018 by hengxin
