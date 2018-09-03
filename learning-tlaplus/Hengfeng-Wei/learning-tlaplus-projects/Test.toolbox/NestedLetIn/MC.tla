---- MODULE MC ----
EXTENDS Test, TLC

\* Constant expression definition @modelExpressionEval
const_expr_15359761874033000 == 
Six
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15359761874033000>>)
----

=============================================================================
\* Modification History
\* Created Mon Sep 03 20:03:07 CST 2018 by hengxin
