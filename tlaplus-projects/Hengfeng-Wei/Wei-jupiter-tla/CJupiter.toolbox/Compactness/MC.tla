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
const_15469313790482000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_15469313790483000 == 
{a, b}
----

\* SYMMETRY definition
symm_15469313790484000 == 
Permutations(const_15469313790483000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_15469313790485000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_15469313790486000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15469313790488000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15469313790489000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Tue Jan 08 15:09:39 CST 2019 by hengxin
