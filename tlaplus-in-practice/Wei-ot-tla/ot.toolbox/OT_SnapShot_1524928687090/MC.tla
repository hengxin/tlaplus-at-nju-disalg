---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152492868506948000 == 
1 .. 4
----

\* Constant expression definition @modelExpressionEval
const_expr_152492868506949000 == 
NonOverlappingIntervals
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152492868506949000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 28 23:18:05 CST 2018 by hengxin
