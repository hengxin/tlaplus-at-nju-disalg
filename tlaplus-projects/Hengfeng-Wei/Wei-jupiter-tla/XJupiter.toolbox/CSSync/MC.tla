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
const_154561849333823000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154561849333824000 == 
{a, b}
----

\* SYMMETRY definition
symm_154561849333825000 == 
Permutations(const_154561849333824000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154561849333826000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154561849333828000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154561849333829000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Mon Dec 24 10:28:13 CST 2018 by hengxin
