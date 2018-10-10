---- MODULE MC ----
EXTENDS CJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_153904950480288000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_153904950480389000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_153904950480390000 == 
Permutations(const_153904950480288000) \union Permutations(const_153904950480389000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_153904950480391000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153904950480393000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153904950480394000 ==
WLSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153904950480395000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Tue Oct 09 09:45:04 CST 2018 by hengxin
