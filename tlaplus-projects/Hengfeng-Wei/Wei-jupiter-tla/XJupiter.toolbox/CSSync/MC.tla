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
const_154641093220437000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154641093220438000 == 
{a, b}
----

\* SYMMETRY definition
symm_154641093220439000 == 
Permutations(const_154641093220438000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154641093220440000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154641093220442000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154641093220443000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 14:35:32 CST 2019 by hengxin
