---- MODULE MC ----
EXTENDS OT, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_1530940437742284000 == 
{"a", "b", "c", "d", "e"}
----

\* CONSTANT definitions @modelParameterConstants:1MaxPr
const_1530940437742285000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:2MaxLen
const_1530940437742286000 == 
5
----

\* Constant expression definition @modelExpressionEval
const_expr_1530940437742288000 == 
CP1
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1530940437742288000>>)
----

=============================================================================
\* Modification History
\* Created Sat Jul 07 13:13:57 CST 2018 by hengxin
