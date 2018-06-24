---- MODULE MC ----
EXTENDS OT, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_152984599849188000 == 
{"a", "b", "c"}
----

\* Constant expression definition @modelExpressionEval
const_expr_152984599849190000 == 
XformOpsOp(Ops, Del3)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152984599849190000>>)
----

=============================================================================
\* Modification History
\* Created Sun Jun 24 21:13:18 CST 2018 by hengxin
