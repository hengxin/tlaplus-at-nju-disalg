---- MODULE MC ----
EXTENDS AbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154643310461550000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154643310461551000 == 
{a, b}
----

\* SYMMETRY definition
symm_154643310461552000 == 
Permutations(const_154643310461551000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154643310461553000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154643310461554000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154643310461656000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154643310461657000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 20:45:04 CST 2019 by hengxin
