---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152534977120626000 == 
1 .. 2
----

\* Constant expression definition @modelExpressionEval
const_expr_152534977120627000 == 
Min({2,5})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152534977120627000>>)
----

=============================================================================
\* Modification History
\* Created Thu May 03 20:16:11 CST 2018 by hengxin
