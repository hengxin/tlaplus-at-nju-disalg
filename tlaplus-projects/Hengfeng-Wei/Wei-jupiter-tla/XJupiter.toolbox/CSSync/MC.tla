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
const_1543923022800159000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1543923022800160000 == 
{a, b}
----

\* SYMMETRY definition
symm_1543923022800161000 == 
Permutations(const_1543923022800160000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1543923022800162000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1543923022800164000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1543923022800165000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Tue Dec 04 19:30:22 CST 2018 by hengxin
