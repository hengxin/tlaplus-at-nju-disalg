---- MODULE MC ----
EXTENDS AbsJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_1544836359616194000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1544836359616195000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_1544836359616196000 == 
Permutations(const_1544836359616195000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1544836359616197000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1544836359617199000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1544836359617200000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Sat Dec 15 09:12:39 CST 2018 by hengxin
