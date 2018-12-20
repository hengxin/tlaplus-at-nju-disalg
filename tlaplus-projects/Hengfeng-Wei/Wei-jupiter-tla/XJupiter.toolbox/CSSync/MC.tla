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
const_154521148477558000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154521148477559000 == 
{a, b}
----

\* SYMMETRY definition
symm_154521148477560000 == 
Permutations(const_154521148477559000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154521148477561000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154521148477563000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154521148477564000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Wed Dec 19 17:24:44 CST 2018 by hengxin
