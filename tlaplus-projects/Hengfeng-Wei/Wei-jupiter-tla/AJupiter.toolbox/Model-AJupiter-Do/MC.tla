---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_1530447955885113000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1Cop
const_1530447955885114000 == 
[c1 |-> <<Ins1>>, c2 |-> <<>>, c3 |-> <<>>]
----

\* CONSTANT definitions @modelParameterConstants:2Char
const_1530447955885115000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:3Server
const_1530447955885116000 == 
"s"
----

\* CONSTANT definitions @modelParameterConstants:4State
const_1530447955885117000 == 
<<"a", "b", "c">>
----

\* Constant expression definition @modelExpressionEval
const_expr_1530447955886118000 == 
Cop
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1530447955886118000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530447955886119000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1530447955886120000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sun Jul 01 20:25:55 CST 2018 by hengxin
