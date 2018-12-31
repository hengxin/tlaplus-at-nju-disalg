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
const_154626169490958000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154626169490959000 == 
{a, b}
----

\* SYMMETRY definition
symm_154626169490960000 == 
Permutations(const_154626169490959000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154626169490961000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154626169491063000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154626169491064000 ==
QC
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 21:08:14 CST 2018 by hengxin
