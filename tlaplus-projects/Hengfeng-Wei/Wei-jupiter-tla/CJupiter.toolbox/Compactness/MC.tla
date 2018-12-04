---- MODULE MC ----
EXTENDS CJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_154390031121716000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154390031121717000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_154390031121718000 == 
Permutations(const_154390031121717000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154390031121719000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154390031121721000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154390031121822000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Tue Dec 04 13:11:51 CST 2018 by hengxin
