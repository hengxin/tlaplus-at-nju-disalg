---- MODULE MC ----
EXTENDS Op, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_1530932773094187000 == 
{"a", "b", "c"}
----

\* Constant expression definition @modelExpressionEval
const_expr_1530932773095189000 == 
Apply([type |-> "Ins", pos |-> 2, ch |-> "x", pr |-> 1], <<>>)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1530932773095189000>>)
----

=============================================================================
\* Modification History
\* Created Sat Jul 07 11:06:13 CST 2018 by hengxin
