---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_15297584414322000 == 
{a, b, c}
----

\* CONSTANT definitions @modelParameterConstants:1Server
const_15297584414323000 == 
s
----

\* CONSTANT definitions @modelParameterConstants:2Char
const_15297584414324000 == 
{'a', 'b', 'c', 'd'}
----

\* Constant expression definition @modelExpressionEval
const_expr_15297584414336000 == 
Apply([type |-> "Del", pos |-> 2], <<'a', 'b', 'c'>>)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15297584414336000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_15297584414337000 ==
FALSE/\cbuf = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_15297584414338000 ==
FALSE/\cbuf' = cbuf
----
=============================================================================
\* Modification History
\* Created Sat Jun 23 20:54:01 CST 2018 by hengxin
