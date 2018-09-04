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
const_1536074614704109000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1536074614704110000 == 
{a, b}
----

\* SYMMETRY definition
symm_1536074614704111000 == 
Permutations(const_1536074614704109000) \union Permutations(const_1536074614704110000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1536074614704112000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1536074614704114000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1536074614704115000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Tue Sep 04 23:23:34 CST 2018 by hengxin
