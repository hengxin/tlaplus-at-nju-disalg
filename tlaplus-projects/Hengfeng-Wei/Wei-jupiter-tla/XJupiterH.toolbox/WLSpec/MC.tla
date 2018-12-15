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
const_1544868279772121000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1544868279772122000 == 
{a, b}
----

\* SYMMETRY definition
symm_1544868279772123000 == 
Permutations(const_1544868279772122000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1544868279772124000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1544868279772126000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1544868279772127000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Sat Dec 15 18:04:39 CST 2018 by hengxin
