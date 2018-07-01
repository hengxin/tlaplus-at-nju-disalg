---- MODULE MC ----
EXTENDS OT, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_153044877076318000 == 
{"a", "b", "c"}
----

\* Constant expression definition @modelExpressionEval
const_expr_153044877076320000 == 
XformOpsOp(Ops, Del3)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_153044877076320000>>)
----

=============================================================================
\* Modification History
\* Created Sun Jul 01 20:39:30 CST 2018 by hengxin
