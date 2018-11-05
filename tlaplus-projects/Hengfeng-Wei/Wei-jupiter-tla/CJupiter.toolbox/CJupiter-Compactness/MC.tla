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
const_154140658389418000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Char
const_154140658389419000 == 
{a, b}
----

\* SYMMETRY definition
symm_154140658389420000 == 
Permutations(const_154140658389418000) \union Permutations(const_154140658389419000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154140658389421000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154140658389423000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154140658389424000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_154140658389425000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Mon Nov 05 16:29:43 CST 2018 by hengxin
