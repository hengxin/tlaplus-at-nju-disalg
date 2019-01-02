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
const_154641085053730000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154641085053731000 == 
{a, b}
----

\* SYMMETRY definition
symm_154641085053732000 == 
Permutations(const_154641085053731000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154641085053733000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154641085053735000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154641085053736000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 14:34:10 CST 2019 by hengxin
