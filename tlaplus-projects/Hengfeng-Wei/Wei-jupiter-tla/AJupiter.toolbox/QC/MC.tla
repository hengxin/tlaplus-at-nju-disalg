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
const_1545983864728191000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1545983864728192000 == 
{a, b}
----

\* SYMMETRY definition
symm_1545983864728193000 == 
Permutations(const_1545983864728192000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1545983864728194000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1545983864728196000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1545983864728197000 ==
QC
----
=============================================================================
\* Modification History
\* Created Fri Dec 28 15:57:44 CST 2018 by hengxin
