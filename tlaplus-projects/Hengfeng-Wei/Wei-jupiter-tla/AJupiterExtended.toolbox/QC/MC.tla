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
const_154631451468779000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154631451468780000 == 
{a, b}
----

\* SYMMETRY definition
symm_154631451468781000 == 
Permutations(const_154631451468780000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154631451468782000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154631451468784000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154631451468785000 ==
QC
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 11:48:34 CST 2019 by hengxin
