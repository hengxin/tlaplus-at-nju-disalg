---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152492837479738000 == 
1 .. 4
----

\* Constant expression definition @modelExpressionEval
const_expr_152492837479739000 == 
NonOverlappingIntervals
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152492837479739000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 28 23:12:54 CST 2018 by hengxin
