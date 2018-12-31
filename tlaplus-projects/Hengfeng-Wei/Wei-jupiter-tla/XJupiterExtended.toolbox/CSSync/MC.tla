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
const_154626078801016000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154626078801017000 == 
{a, b}
----

\* SYMMETRY definition
symm_154626078801018000 == 
Permutations(const_154626078801017000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154626078801119000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154626078801121000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154626078801122000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 20:53:08 CST 2018 by hengxin
