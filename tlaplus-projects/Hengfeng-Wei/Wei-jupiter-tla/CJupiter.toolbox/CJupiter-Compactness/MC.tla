---- MODULE MC ----
EXTENDS CJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154142445576652000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Char
const_154142445576753000 == 
{a, b}
----

\* SYMMETRY definition
symm_154142445576754000 == 
Permutations(const_154142445576652000) \union Permutations(const_154142445576753000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154142445576755000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154142445576757000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154142445576758000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_154142445576759000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Mon Nov 05 21:27:35 CST 2018 by hengxin
