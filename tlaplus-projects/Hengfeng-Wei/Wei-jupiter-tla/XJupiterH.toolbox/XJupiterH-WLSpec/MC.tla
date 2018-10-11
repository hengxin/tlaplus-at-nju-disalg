---- MODULE MC ----
EXTENDS XJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_15391618778582000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Char
const_15391618778583000 == 
{a, b}
----

\* SYMMETRY definition
symm_15391618778584000 == 
Permutations(const_15391618778582000) \union Permutations(const_15391618778583000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_15391618778585000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15391618778587000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15391618778598000 ==
TypeOKH
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_15391618778599000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Wed Oct 10 16:57:57 CST 2018 by hengxin
