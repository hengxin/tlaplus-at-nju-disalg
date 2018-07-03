---- MODULE MC ----
EXTENDS OT, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_1530604991361129000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:1MaxPos
const_1530604991361130000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2MaxPr
const_1530604991361131000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3MaxLen
const_1530604991361132000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_1530604991361134000 == 
CP1
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1530604991361134000>>)
----

=============================================================================
\* Modification History
\* Created Tue Jul 03 16:03:11 CST 2018 by hengxin
