---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152534910880614000 == 
1 .. 2
----

\* Constant expression definition @modelExpressionEval
const_expr_152534910880615000 == 
IntSeqs
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152534910880615000>>)
----

=============================================================================
\* Modification History
\* Created Thu May 03 20:05:08 CST 2018 by hengxin
