---- MODULE MC ----
EXTENDS GCD, TLC

\* Constant expression definition @modelExpressionEval
const_expr_15297594568725000 == 
GCD(1503, 1503)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15297594568725000>>)
----

=============================================================================
\* Modification History
\* Created Sat Jun 23 21:10:56 CST 2018 by hengxin
