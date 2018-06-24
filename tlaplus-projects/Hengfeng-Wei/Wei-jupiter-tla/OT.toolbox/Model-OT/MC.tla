---- MODULE MC ----
EXTENDS OT, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_152983455937285000 == 
{"a", "b", "c"}
----

\* Constant expression definition @modelExpressionEval
const_expr_152983455937287000 == 
XformOpsOp(Ops, Del3)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_152983455937287000>>)
----

=============================================================================
\* Modification History
\* Created Sun Jun 24 18:02:39 CST 2018 by hengxin
