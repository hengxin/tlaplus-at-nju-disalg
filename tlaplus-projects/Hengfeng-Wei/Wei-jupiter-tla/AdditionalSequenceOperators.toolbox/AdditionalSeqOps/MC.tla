---- MODULE MC ----
EXTENDS AdditionalSequenceOperators, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1534087101985471000 == 
LCSCompatibleTest({1,2,3,4,5})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1534087101985471000>>)
----

=============================================================================
\* Modification History
\* Created Sun Aug 12 23:18:21 CST 2018 by hengxin
