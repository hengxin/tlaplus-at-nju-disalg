---- MODULE MC ----
EXTENDS AdditionalSequenceOperators, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1530674583587162000 == 
InsertElement(<<>>, "a", 100)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1530674583587162000>>)
----

=============================================================================
\* Modification History
\* Created Wed Jul 04 11:23:03 CST 2018 by hengxin
