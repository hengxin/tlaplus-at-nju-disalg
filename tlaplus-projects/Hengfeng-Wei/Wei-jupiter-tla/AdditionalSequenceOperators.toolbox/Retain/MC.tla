---- MODULE MC ----
EXTENDS AdditionalSequenceOperators, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1537877516003225000 == 
Retain(<<1, 8,6, 3,2, 3,5,7>>, {})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1537877516003225000>>)
----

=============================================================================
\* Modification History
\* Created Tue Sep 25 20:11:56 CST 2018 by hengxin
