---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_152492231884939000 == 
1 .. 5
----

\* Constant expression definition @modelExpressionEval
const_expr_152492231884940000 == 
NonOverlappingIntervals
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152492231884940000>>)
----

=============================================================================
\* Modification History
\* Created Sat Apr 28 21:31:58 CST 2018 by hengxin
