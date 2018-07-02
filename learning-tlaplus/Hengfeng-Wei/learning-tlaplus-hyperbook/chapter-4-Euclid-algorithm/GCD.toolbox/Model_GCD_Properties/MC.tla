---- MODULE MC ----
EXTENDS GCD, TLC

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_15236050495784000 ==
1 .. 10
----
\* Constant expression definition @modelExpressionEval
const_expr_15236050495785000 == 
\A m \in Nat \ {0}, n \in Nat \ {0} : GCD(m,m) = m /\ GCD(m,n) = GCD(n,m) /\ (n > m) => (GCD(m,n) = GCD(m, n-m))
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_15236050495785000>>)
----

=============================================================================
\* Modification History
\* Created Fri Apr 13 15:37:29 CST 2018 by hengxin
