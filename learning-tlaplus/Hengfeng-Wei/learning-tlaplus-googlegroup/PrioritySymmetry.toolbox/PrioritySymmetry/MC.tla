---- MODULE MC ----
EXTENDS PrioritySymmetry, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT definitions Client
const_154381640271858000 == 
{c1, c2, c3}
----

\* SYMMETRY definition
symm_154381640271859000 == 
Permutations(const_154381640271858000)
----

\* CONSTANT definitions @modelParameterConstants:0N
const_154381640271860000 == 
1
----

\* Constant expression definition @modelExpressionEval
const_expr_154381640271861000 == 
Priority
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_154381640271861000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154381640271862000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Mon Dec 03 13:53:22 CST 2018 by hengxin
