---- MODULE MC ----
EXTENDS AdditionalSequenceOperators, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1534073889678302000 == 
LCSCompatibleTest({1,2,3,4,5,6,7})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1534073889678302000>>)
----

=============================================================================
\* Modification History
\* Created Sun Aug 12 19:38:09 CST 2018 by hengxin
