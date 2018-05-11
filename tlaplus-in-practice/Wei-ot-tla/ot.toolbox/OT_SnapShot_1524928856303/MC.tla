---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152492885428052000 == 
1 .. 5
----

\* Constant expression definition @modelExpressionEval
const_expr_152492885428053000 == 
NonOverlappingIntervals
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152492885428053000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 28 23:20:54 CST 2018 by hengxin
