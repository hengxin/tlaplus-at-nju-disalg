---- MODULE MC ----
EXTENDS CJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154701477800618000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154701477800619000 == 
{a, b}
----

\* SYMMETRY definition
symm_154701477800620000 == 
Permutations(const_154701477800619000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154701477800621000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154701477800622000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154701477800624000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154701477800625000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Wed Jan 09 14:19:38 CST 2019 by hengxin
