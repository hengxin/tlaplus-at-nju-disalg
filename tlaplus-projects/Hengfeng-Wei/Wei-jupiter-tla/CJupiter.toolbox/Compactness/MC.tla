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
const_154561902912037000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154561902912038000 == 
{a, b}
----

\* SYMMETRY definition
symm_154561902912039000 == 
Permutations(const_154561902912038000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154561902912040000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154561902912042000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154561902912043000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Mon Dec 24 10:37:09 CST 2018 by hengxin
