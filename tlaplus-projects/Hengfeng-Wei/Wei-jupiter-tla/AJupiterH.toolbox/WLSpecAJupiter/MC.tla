---- MODULE MC ----
EXTENDS AJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154591408636563000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154591408636564000 == 
{a, b}
----

\* SYMMETRY definition
symm_154591408636565000 == 
Permutations(const_154591408636564000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154591408636566000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154591408636568000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154591408636569000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Thu Dec 27 20:34:46 CST 2018 by hengxin
