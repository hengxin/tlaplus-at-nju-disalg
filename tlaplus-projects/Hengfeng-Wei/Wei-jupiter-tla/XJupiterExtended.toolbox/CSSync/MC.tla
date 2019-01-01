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
const_154631416139058000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154631416139059000 == 
{a, b}
----

\* SYMMETRY definition
symm_154631416139060000 == 
Permutations(const_154631416139059000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154631416139061000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154631416139063000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154631416139064000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 11:42:41 CST 2019 by hengxin
