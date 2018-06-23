---- MODULE MC ----
EXTENDS Op, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_15297598989505000 == 
{'a', 'b', 'c'}
----

\* Constant expression definition @modelExpressionEval
const_expr_15297598989507000 == 
Apply([type |-> "Del", pos |-> 2], <<'a', 'b', 'c'>>)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15297598989507000>>)
----

=============================================================================
\* Modification History
\* Created Sat Jun 23 21:18:18 CST 2018 by hengxin
