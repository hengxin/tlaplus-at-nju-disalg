---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152492834529636000 == 
1 .. 4
----

\* Constant expression definition @modelExpressionEval
const_expr_152492834529637000 == 
NonOverlappingIntervals
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152492834529637000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 28 23:12:25 CST 2018 by hengxin
