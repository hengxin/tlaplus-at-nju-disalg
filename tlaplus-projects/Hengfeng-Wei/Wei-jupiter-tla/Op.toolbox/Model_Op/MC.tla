---- MODULE MC ----
EXTENDS Op, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_152976119059876000 == 
{"a", "b", "c"}
----

\* Constant expression definition @modelExpressionEval
const_expr_152976119059878000 == 
Apply([type |-> "Ins", pos |-> 5, ch |-> "x"], <<"a","b","c">>)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152976119059878000>>)
----

=============================================================================
\* Modification History
\* Created Sat Jun 23 21:39:50 CST 2018 by hengxin
