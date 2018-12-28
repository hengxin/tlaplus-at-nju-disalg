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
const_154596656395816000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154596656395817000 == 
{a, b}
----

\* SYMMETRY definition
symm_154596656395818000 == 
Permutations(const_154596656395817000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154596656395819000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154596656395821000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154596656395822000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Fri Dec 28 11:09:23 CST 2018 by hengxin
