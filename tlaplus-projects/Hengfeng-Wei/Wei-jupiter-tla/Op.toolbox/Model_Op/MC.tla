---- MODULE MC ----
EXTENDS Op, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_153043554150216000 == 
{"a", "b", "c"}
----

\* Constant expression definition @modelExpressionEval
const_expr_153043554150218000 == 
Apply([type |-> "Ins", pos |-> 5, ch |-> "x"], <<"a","b","c">>)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_153043554150218000>>)
----

=============================================================================
\* Modification History
\* Created Sun Jul 01 16:59:01 CST 2018 by hengxin
