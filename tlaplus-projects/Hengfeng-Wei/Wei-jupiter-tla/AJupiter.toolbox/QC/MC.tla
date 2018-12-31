---- MODULE MC ----
EXTENDS AJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154626143550144000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154626143550145000 == 
{a, b}
----

\* SYMMETRY definition
symm_154626143550146000 == 
Permutations(const_154626143550145000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154626143550147000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154626143550149000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154626143550150000 ==
QC
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 21:03:55 CST 2018 by hengxin
