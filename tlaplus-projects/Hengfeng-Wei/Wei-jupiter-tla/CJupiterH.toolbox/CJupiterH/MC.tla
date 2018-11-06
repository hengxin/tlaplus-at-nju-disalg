---- MODULE MC ----
EXTENDS CJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1541508100995204000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1541508100995205000 == 
{a, b}
----

\* SYMMETRY definition
symm_1541508100995206000 == 
Permutations(const_1541508100995204000) \union Permutations(const_1541508100995205000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1541508100995207000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1541508100995209000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1541508100995210000 ==
WLSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1541508100995211000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Tue Nov 06 20:41:40 CST 2018 by hengxin
