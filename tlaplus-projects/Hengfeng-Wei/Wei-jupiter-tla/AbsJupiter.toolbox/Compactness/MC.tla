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
const_15466793420222000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_15466793420223000 == 
{a, b}
----

\* SYMMETRY definition
symm_15466793420224000 == 
Permutations(const_15466793420223000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_15466793420225000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_15466793420226000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15466793420238000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15466793420239000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Sat Jan 05 17:09:02 CST 2019 by hengxin
