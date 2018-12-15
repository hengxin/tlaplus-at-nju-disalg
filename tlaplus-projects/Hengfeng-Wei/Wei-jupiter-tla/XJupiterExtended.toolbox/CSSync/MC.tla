---- MODULE MC ----
EXTENDS XJupiterExtended, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1544868129584100000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1544868129584101000 == 
{a, b}
----

\* SYMMETRY definition
symm_1544868129584102000 == 
Permutations(const_1544868129584101000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1544868129584103000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1544868129584105000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1544868129584106000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Sat Dec 15 18:02:09 CST 2018 by hengxin
