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
const_1541507738558188000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1541507738558189000 == 
{a, b}
----

\* SYMMETRY definition
symm_1541507738558190000 == 
Permutations(const_1541507738558188000) \union Permutations(const_1541507738558189000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1541507738558191000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1541507738559193000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1541507738559194000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1541507738559195000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Tue Nov 06 20:35:38 CST 2018 by hengxin
