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
const_154650505484146000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154650505484147000 == 
{a, b}
----

\* SYMMETRY definition
symm_154650505484148000 == 
Permutations(const_154650505484147000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154650505484149000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154650505484150000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154650505484152000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154650505484153000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Thu Jan 03 16:44:14 CST 2019 by hengxin
