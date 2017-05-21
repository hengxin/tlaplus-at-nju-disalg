---- MODULE MC ----
EXTENDS GCD, TLC

\* Constant expression definition @modelExpressionEval
const_expr_146625175512841000 == 
GCD(1503, 1503)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_146625175512841000>>)
----

=============================================================================
\* Modification History
\* Created Sat Jun 18 20:09:15 CST 2016 by hengxin
