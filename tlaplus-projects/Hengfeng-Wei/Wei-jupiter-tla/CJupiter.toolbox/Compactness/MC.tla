---- MODULE MC ----
EXTENDS CJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_15459663756689000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154596637566810000 == 
{a, b}
----

\* SYMMETRY definition
symm_154596637566811000 == 
Permutations(const_154596637566810000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154596637566812000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154596637566814000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154596637566815000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Fri Dec 28 11:06:15 CST 2018 by hengxin
