---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_15253489959432000 == 
1 .. 5
----

\* Constant expression definition @modelExpressionEval
const_expr_15253489959463000 == 
NonOverlappingIntervals
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15253489959463000>>)
----

=============================================================================
\* Modification History
\* Created Thu May 03 20:03:15 CST 2018 by hengxin
