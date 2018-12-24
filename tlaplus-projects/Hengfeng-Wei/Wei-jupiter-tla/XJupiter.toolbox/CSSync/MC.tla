---- MODULE MC ----
EXTENDS XJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154561921004751000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154561921004752000 == 
{a, b}
----

\* SYMMETRY definition
symm_154561921004753000 == 
Permutations(const_154561921004752000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154561921004754000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154561921004756000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154561921004757000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Mon Dec 24 10:40:10 CST 2018 by hengxin
