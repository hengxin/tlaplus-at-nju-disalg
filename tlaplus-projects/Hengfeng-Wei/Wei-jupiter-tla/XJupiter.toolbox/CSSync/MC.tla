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
const_154521596125316000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154521596125317000 == 
{a, b}
----

\* SYMMETRY definition
symm_154521596125318000 == 
Permutations(const_154521596125317000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154521596125319000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154521596125421000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154521596125422000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Wed Dec 19 18:39:21 CST 2018 by hengxin
