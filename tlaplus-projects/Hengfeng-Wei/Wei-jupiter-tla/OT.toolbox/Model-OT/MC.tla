---- MODULE MC ----
EXTENDS OT, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_1530716156946565000 == 
{"a", "b", "c", "d", "e", "f", "g"}
----

\* CONSTANT definitions @modelParameterConstants:1MaxPos
const_1530716156946566000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:2MaxPr
const_1530716156946567000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:3MaxLen
const_1530716156946568000 == 
6
----

\* Constant expression definition @modelExpressionEval
const_expr_1530716156946570000 == 
CP1
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1530716156946570000>>)
----

=============================================================================
\* Modification History
\* Created Wed Jul 04 22:55:56 CST 2018 by hengxin
