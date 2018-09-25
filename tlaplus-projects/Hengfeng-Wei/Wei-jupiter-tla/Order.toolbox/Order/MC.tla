---- MODULE MC ----
EXTENDS Order, TLC

\* Constant expression definition @modelExpressionEval
const_expr_153786858555213000 == 
LT({<<1,2>>, <<1,3>>, <<2,4>>}, 5)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_153786858555213000>>)
----

=============================================================================
\* Modification History
\* Created Tue Sep 25 17:43:05 CST 2018 by hengxin
