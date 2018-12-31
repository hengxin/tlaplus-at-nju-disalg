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
const_154625928656630000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154625928656631000 == 
{a, b}
----

\* SYMMETRY definition
symm_154625928656632000 == 
Permutations(const_154625928656631000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154625928656633000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154625928656635000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154625928656636000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 20:28:06 CST 2018 by hengxin
