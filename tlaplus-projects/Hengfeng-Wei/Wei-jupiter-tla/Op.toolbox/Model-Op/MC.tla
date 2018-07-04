---- MODULE MC ----
EXTENDS Op, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_1530674930095169000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:1MaxPos
const_1530674930096170000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2MaxPr
const_1530674930096171000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3MaxLen
const_1530674930096172000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_1530674930096174000 == 
Apply([type |-> "Ins", pos |-> 1, ch |-> "x", pr |-> 1], <<>>)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1530674930096174000>>)
----

=============================================================================
\* Modification History
\* Created Wed Jul 04 11:28:50 CST 2018 by hengxin
