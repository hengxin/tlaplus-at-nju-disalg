---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_15299304737218000 == 
{a, b, c}
----

\* CONSTANT definitions @modelParameterConstants:1Server
const_15299304737219000 == 
s
----

\* CONSTANT definitions @modelParameterConstants:2Char
const_152993047372110000 == 
{'a', 'b', 'c', 'd'}
----

\* Constant expression definition @modelExpressionEval
const_expr_152993047372112000 == 
Apply([type |-> "Del", pos |-> 2], <<'a', 'b', 'c'>>)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152993047372112000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_152993047372113000 ==
FALSE/\cbuf = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_152993047372114000 ==
FALSE/\cbuf' = cbuf
----
=============================================================================
\* Modification History
\* Created Mon Jun 25 20:41:13 CST 2018 by hengxin
