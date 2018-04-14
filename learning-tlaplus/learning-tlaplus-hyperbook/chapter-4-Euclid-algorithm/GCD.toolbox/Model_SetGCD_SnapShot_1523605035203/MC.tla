---- MODULE MC ----
EXTENDS GCD, TLC

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_15236050319412000 ==
1 .. 1000
----
\* Constant expression definition @modelExpressionEval
const_expr_15236050319413000 == 
SetGCD({100, 200, 350, 310, 35, 289})
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15236050319413000>>)
----

=============================================================================
\* Modification History
\* Created Fri Apr 13 15:37:11 CST 2018 by hengxin
