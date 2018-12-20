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
const_154519060662516000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154519060662517000 == 
{a, b}
----

\* SYMMETRY definition
symm_154519060662518000 == 
Permutations(const_154519060662517000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154519060662519000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154519060662521000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154519060662522000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Wed Dec 19 11:36:46 CST 2018 by hengxin
