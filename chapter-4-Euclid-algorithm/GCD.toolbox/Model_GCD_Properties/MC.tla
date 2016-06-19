---- MODULE MC ----
EXTENDS GCD, TLC

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_146633930769243000 ==
1 .. 10
----
\* Constant expression definition @modelExpressionEval
const_expr_146633930770244000 == 
\A m \in Nat \ {0}, n \in Nat \ {0} : GCD(m,m) = m /\ GCD(m,n) = GCD(n,m) /\ (n > m) => (GCD(m,n) = GCD(m, n-m))
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_146633930770244000>>)
----

=============================================================================
\* Modification History
\* Created Sun Jun 19 20:28:27 CST 2016 by hengxin
