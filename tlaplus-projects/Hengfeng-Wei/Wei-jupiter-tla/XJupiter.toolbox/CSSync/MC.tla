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
const_154622553561516000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154622553561517000 == 
{a, b}
----

\* SYMMETRY definition
symm_154622553561518000 == 
Permutations(const_154622553561517000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154622553561519000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154622553561521000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154622553561522000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 11:05:35 CST 2018 by hengxin
