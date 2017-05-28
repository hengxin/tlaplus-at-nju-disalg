---- MODULE MC ----
EXTENDS GCD, TLC

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_146639496982353000 ==
1 .. 1000
----
\* Constant expression definition @modelExpressionEval
const_expr_146639496983354000 == 
SetGCD({100, 200, 350, 310, 35, 289})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_146639496983354000>>)
----

=============================================================================
\* Modification History
\* Created Mon Jun 20 11:56:09 CST 2016 by hengxin
