---- MODULE MC ----
EXTENDS AdditionalSequenceOperators, TLC

\* Constant expression definition @modelExpressionEval
const_expr_154142347999311000 == 
FirstIndexOfElementSafe(<<2,3,4,5,1,4,5>>, 5)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_154142347999311000>>)
----

=============================================================================
\* Modification History
\* Created Mon Nov 05 21:11:19 CST 2018 by hengxin
