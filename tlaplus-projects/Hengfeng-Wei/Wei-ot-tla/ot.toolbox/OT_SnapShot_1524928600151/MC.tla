---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152492859813746000 == 
1 .. 4
----

\* Constant expression definition @modelExpressionEval
const_expr_152492859813747000 == 
NonOverlappingIntervals
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152492859813747000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 28 23:16:38 CST 2018 by hengxin
