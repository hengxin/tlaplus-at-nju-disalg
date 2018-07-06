---- MODULE MC ----
EXTENDS OT, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_1530864569281631000 == 
{"a", "b", "c", "d", "e"}
----

\* CONSTANT definitions @modelParameterConstants:1MaxPos
const_1530864569281632000 == 
7
----

\* CONSTANT definitions @modelParameterConstants:2MaxPr
const_1530864569281633000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:3MaxLen
const_1530864569281634000 == 
6
----

\* Constant expression definition @modelExpressionEval
const_expr_1530864569281636000 == 
CP1
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1530864569281636000>>)
----

=============================================================================
\* Modification History
\* Created Fri Jul 06 16:09:29 CST 2018 by hengxin
