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
const_154486681697137000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154486681697138000 == 
{a, b}
----

\* SYMMETRY definition
symm_154486681697139000 == 
Permutations(const_154486681697138000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154486681697140000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154486681697242000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154486681697243000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Sat Dec 15 17:40:16 CST 2018 by hengxin
