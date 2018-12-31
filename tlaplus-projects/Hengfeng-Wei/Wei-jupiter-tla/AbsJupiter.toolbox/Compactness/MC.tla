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
const_15462247898772000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_15462247898773000 == 
{a, b}
----

\* SYMMETRY definition
symm_15462247898774000 == 
Permutations(const_15462247898773000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_15462247898775000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15462247898777000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15462247898778000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 10:53:09 CST 2018 by hengxin
