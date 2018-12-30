---- MODULE MC ----
EXTENDS AJupiterExtended, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154608099223879000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154608099223880000 == 
{a, b}
----

\* SYMMETRY definition
symm_154608099223881000 == 
Permutations(const_154608099223880000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154608099223882000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154608099223884000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154608099223885000 ==
TypeOKEx
----
=============================================================================
\* Modification History
\* Created Sat Dec 29 18:56:32 CST 2018 by hengxin
