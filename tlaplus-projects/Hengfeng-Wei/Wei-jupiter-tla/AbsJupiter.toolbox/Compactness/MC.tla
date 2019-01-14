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
const_154743388504826000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154743388504827000 == 
{a, b}
----

\* SYMMETRY definition
symm_154743388504828000 == 
Permutations(const_154743388504827000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154743388504829000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154743388504830000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154743388504832000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154743388504833000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Mon Jan 14 10:44:45 CST 2019 by hengxin
