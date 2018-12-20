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
const_15452157548399000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154521575483910000 == 
{a, b}
----

\* SYMMETRY definition
symm_154521575483911000 == 
Permutations(const_154521575483910000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154521575483912000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154521575483914000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154521575483915000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Wed Dec 19 18:35:54 CST 2018 by hengxin
