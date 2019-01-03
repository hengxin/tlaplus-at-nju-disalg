---- MODULE MC ----
EXTENDS AJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_154650428851239000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154650428851240000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_154650428851241000 == 
Permutations(const_154650428851240000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154650428851242000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154650428851244000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154650428851245000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Thu Jan 03 16:31:28 CST 2019 by hengxin
