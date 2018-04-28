---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152492112114415000 == 
1 .. 3
----

\* Constant expression definition @modelExpressionEval
const_expr_152492112114416000 == 
NonOverlappingIntervals
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152492112114416000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 28 21:12:01 CST 2018 by hengxin
