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
const_154175179566420000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154175179566421000 == 
{a, b}
----

\* SYMMETRY definition
symm_154175179566422000 == 
Permutations(const_154175179566420000) \union Permutations(const_154175179566421000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154175179566423000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154175179566425000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154175179566426000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_154175179566427000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Fri Nov 09 16:23:15 CST 2018 by hengxin
