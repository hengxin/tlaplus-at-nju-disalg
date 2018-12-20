---- MODULE MC ----
EXTENDS RGAH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT definitions Char
const_15451069823712000 == 
{a, b, c}
----

\* MV CONSTANT definitions Replica
const_15451069823713000 == 
{r1, r2}
----

\* SYMMETRY definition
symm_15451069823714000 == 
Permutations(const_15451069823712000) \union Permutations(const_15451069823713000)
----

\* CONSTANT definitions @modelParameterConstants:0Charnum
const_15451069823715000 == 
3
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_15451069823716000 ==
1..10
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15451069823717000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15451069823718000 ==
TypeOKH
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_15451069823719000 ==
EC
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_154510698237110000 ==
WLSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:3
inv_154510698237111000 ==
SLSpec
----
=============================================================================
\* Modification History
\* Created Tue Dec 18 12:23:02 CST 2018 by xhdn
