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
const_154650416948717000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154650416948718000 == 
{a, b}
----

\* SYMMETRY definition
symm_154650416948719000 == 
Permutations(const_154650416948718000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154650416948720000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154650416948721000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154650416948723000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154650416948724000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Thu Jan 03 16:29:29 CST 2019 by hengxin
