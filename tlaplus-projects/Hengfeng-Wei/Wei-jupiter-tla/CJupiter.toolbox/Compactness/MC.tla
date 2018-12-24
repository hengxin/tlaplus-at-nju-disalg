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
const_154561831551016000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154561831551017000 == 
{a, b}
----

\* SYMMETRY definition
symm_154561831551018000 == 
Permutations(const_154561831551017000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154561831551019000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154561831551021000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154561831551022000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Mon Dec 24 10:25:15 CST 2018 by hengxin
