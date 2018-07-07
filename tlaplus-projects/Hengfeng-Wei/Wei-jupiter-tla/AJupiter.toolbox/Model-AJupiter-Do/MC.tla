---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_153094634082866000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1Cop
const_153094634082867000 == 
[c1 |-> <<Ins1>>, c2 |-> <<>>, c3 |-> <<>>]
----

\* CONSTANT definitions @modelParameterConstants:2Char
const_153094634082868000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:3Server
const_153094634082869000 == 
"s"
----

\* CONSTANT definitions @modelParameterConstants:4InitState
const_153094634082870000 == 
<<"a", "b">>
----

\* Constant expression definition @modelExpressionEval
const_expr_153094634082872000 == 
cVars \o sVars \o <<cincoming, sincoming>>
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_153094634082872000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153094634082873000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153094634082874000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sat Jul 07 14:52:20 CST 2018 by hengxin
