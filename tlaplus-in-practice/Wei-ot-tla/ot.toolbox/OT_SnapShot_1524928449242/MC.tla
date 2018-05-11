---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152492844721242000 == 
1 .. 4
----

\* Constant expression definition @modelExpressionEval
const_expr_152492844721243000 == 
NonOverlappingIntervals
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152492844721243000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 28 23:14:07 CST 2018 by hengxin
