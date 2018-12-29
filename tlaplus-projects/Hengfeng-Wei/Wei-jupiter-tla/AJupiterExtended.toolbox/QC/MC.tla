---- MODULE MC ----
EXTENDS AJupiterExtended, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154607670213444000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154607670213445000 == 
{a, b}
----

\* SYMMETRY definition
symm_154607670213446000 == 
Permutations(const_154607670213445000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154607670213447000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154607670213449000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154607670213450000 ==
QC
----
=============================================================================
\* Modification History
\* Created Sat Dec 29 17:45:02 CST 2018 by hengxin
