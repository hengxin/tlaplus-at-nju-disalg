---- MODULE MC ----
EXTENDS XJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1539486590670125000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1539486590670126000 == 
{a, b}
----

\* SYMMETRY definition
symm_1539486590670127000 == 
Permutations(const_1539486590670125000) \union Permutations(const_1539486590670126000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1539486590670128000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1539486590670130000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1539486590670131000 ==
TypeOKH
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1539486590670132000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Sun Oct 14 11:09:50 CST 2018 by hengxin
