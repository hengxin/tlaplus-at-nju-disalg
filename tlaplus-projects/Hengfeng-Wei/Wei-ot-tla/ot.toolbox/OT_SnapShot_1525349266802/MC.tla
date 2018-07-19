---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152534926477718000 == 
1 .. 2
----

\* Constant expression definition @modelExpressionEval
const_expr_152534926477719000 == 
NonOverlappingIntervals
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152534926477719000>>)
----

=============================================================================
\* Modification History
\* Created Thu May 03 20:07:44 CST 2018 by hengxin
