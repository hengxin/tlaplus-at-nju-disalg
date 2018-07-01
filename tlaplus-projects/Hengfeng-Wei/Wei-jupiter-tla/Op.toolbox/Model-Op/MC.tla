---- MODULE MC ----
EXTENDS Op, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_153044250105821000 == 
{"a", "b", "c"}
----

\* Constant expression definition @modelExpressionEval
const_expr_153044250105923000 == 
Apply([type |-> "Ins", pos |-> 1, ch |-> "x", pr |-> 1], <<>>)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_153044250105923000>>)
----

=============================================================================
\* Modification History
\* Created Sun Jul 01 18:55:01 CST 2018 by hengxin
