---- MODULE MC ----
EXTENDS AbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_15473456130372000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_15473456130373000 == 
{a, b}
----

\* SYMMETRY definition
symm_15473456130374000 == 
Permutations(const_15473456130373000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_15473456130375000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_15473456130376000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15473456130378000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15473456130379000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Sun Jan 13 10:13:33 CST 2019 by hengxin
