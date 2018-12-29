---- MODULE MC ----
EXTENDS AJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_154605076498330000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154605076498331000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_154605076498332000 == 
Permutations(const_154605076498331000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154605076498333000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154605076498335000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154605076498336000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Sat Dec 29 10:32:44 CST 2018 by hengxin
