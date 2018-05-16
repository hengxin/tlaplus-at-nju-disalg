---- MODULE MC ----
EXTENDS ot, TLC

\* CONSTANT definitions @modelParameterConstants:0POS
const_15253490154556000 == 
1 .. 3
----

\* Constant expression definition @modelExpressionEval
const_expr_15253490154557000 == 
NonOverlappingIntervals
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15253490154557000>>)
----

=============================================================================
\* Modification History
\* Created Thu May 03 20:03:35 CST 2018 by hengxin
