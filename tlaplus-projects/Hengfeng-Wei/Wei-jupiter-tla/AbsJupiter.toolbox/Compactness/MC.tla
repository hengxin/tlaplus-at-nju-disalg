---- MODULE MC ----
EXTENDS AbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_15459662863802000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_15459662863803000 == 
{a, b}
----

\* SYMMETRY definition
symm_15459662863804000 == 
Permutations(const_15459662863803000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_15459662863805000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15459662863817000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15459662863818000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Fri Dec 28 11:04:46 CST 2018 by hengxin
