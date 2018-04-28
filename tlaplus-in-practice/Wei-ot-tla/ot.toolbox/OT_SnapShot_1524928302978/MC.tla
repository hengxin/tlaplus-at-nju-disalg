---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152492830095034000 == 
1 .. 4
----

\* Constant expression definition @modelExpressionEval
const_expr_152492830095035000 == 
NonOverlappingIntervals
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152492830095035000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 28 23:11:40 CST 2018 by hengxin
