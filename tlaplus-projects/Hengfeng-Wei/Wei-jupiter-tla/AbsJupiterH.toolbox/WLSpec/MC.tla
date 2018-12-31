---- MODULE MC ----
EXTENDS AbsJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154625934920637000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154625934920638000 == 
{a, b}
----

\* SYMMETRY definition
symm_154625934920639000 == 
Permutations(const_154625934920638000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154625934920640000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154625934920642000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154625934920643000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 20:29:09 CST 2018 by hengxin
