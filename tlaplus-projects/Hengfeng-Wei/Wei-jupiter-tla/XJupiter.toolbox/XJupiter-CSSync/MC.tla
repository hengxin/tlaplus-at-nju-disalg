---- MODULE MC ----
EXTENDS XJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_15397440365602000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_15397440365603000 == 
{a, b}
----

\* SYMMETRY definition
symm_15397440365604000 == 
Permutations(const_15397440365602000) \union Permutations(const_15397440365603000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_15397440365605000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15397440365607000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15397440365608000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Wed Oct 17 10:40:36 CST 2018 by hengxin
