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
const_154643392846698000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154643392846699000 == 
{a, b}
----

\* SYMMETRY definition
symm_1546433928466100000 == 
Permutations(const_154643392846699000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1546433928466101000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1546433928466102000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1546433928466104000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1546433928466105000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 20:58:48 CST 2019 by hengxin
