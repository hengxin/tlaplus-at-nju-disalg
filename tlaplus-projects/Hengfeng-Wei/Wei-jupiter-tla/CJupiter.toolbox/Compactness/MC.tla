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
const_154631391950944000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154631391950945000 == 
{a, b}
----

\* SYMMETRY definition
symm_154631391950946000 == 
Permutations(const_154631391950945000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154631391950947000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154631391950949000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154631391950950000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 11:38:39 CST 2019 by hengxin
