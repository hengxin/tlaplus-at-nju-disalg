---- MODULE MC ----
EXTENDS AbsJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154643339269066000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154643339269067000 == 
{a, b}
----

\* SYMMETRY definition
symm_154643339269068000 == 
Permutations(const_154643339269067000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154643339269069000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154643339269070000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154643339269172000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154643339269173000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 20:49:52 CST 2019 by hengxin
