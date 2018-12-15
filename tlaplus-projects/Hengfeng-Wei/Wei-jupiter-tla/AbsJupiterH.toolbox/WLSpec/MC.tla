---- MODULE MC ----
EXTENDS AbsJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154486601622223000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154486601622224000 == 
{a, b}
----

\* SYMMETRY definition
symm_154486601622225000 == 
Permutations(const_154486601622224000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154486601622226000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154486601622228000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154486601622229000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Sat Dec 15 17:26:56 CST 2018 by hengxin
