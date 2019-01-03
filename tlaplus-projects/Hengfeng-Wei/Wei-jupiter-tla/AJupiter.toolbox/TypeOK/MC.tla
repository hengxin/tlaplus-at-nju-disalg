---- MODULE MC ----
EXTENDS AJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154650424008425000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154650424008426000 == 
{a, b}
----

\* SYMMETRY definition
symm_154650424008427000 == 
Permutations(const_154650424008426000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154650424008428000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154650424008430000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154650424008431000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Thu Jan 03 16:30:40 CST 2019 by hengxin
