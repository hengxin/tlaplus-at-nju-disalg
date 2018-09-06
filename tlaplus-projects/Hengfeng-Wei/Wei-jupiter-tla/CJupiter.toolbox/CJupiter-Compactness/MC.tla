---- MODULE MC ----
EXTENDS CJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a
----

\* MV CONSTANT definitions Client
const_153623961549052000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Char
const_153623961549053000 == 
{a}
----

\* SYMMETRY definition
symm_153623961549054000 == 
Permutations(const_153623961549052000) \union Permutations(const_153623961549053000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_153623961549055000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153623961549157000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153623961549158000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153623961549159000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Thu Sep 06 21:13:35 CST 2018 by hengxin
