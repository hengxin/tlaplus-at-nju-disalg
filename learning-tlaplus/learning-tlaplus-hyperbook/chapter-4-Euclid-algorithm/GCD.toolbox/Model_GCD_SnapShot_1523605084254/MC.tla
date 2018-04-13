---- MODULE MC ----
EXTENDS GCD, TLC

\* Constant expression definition @modelExpressionEval
const_expr_15236050812176000 == 
GCD(1503, 1503)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15236050812176000>>)
----

=============================================================================
\* Modification History
\* Created Fri Apr 13 15:38:01 CST 2018 by hengxin
