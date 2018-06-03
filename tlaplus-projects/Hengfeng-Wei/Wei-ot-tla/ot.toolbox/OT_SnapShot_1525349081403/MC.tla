---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152534907936910000 == 
1 .. 3
----

\* Constant expression definition @modelExpressionEval
const_expr_152534907936911000 == 
IntSeqs
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152534907936911000>>)
----

=============================================================================
\* Modification History
\* Created Thu May 03 20:04:39 CST 2018 by hengxin
