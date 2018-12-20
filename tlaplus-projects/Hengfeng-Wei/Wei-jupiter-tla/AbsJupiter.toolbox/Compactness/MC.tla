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
const_154514291156516000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154514291156517000 == 
{a, b}
----

\* SYMMETRY definition
symm_154514291156518000 == 
Permutations(const_154514291156517000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154514291156519000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154514291156521000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154514291156522000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Tue Dec 18 22:21:51 CST 2018 by hengxin
