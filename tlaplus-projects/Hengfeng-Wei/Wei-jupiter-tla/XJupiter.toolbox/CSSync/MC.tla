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
const_154562267411823000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154562267411824000 == 
{a, b}
----

\* SYMMETRY definition
symm_154562267411825000 == 
Permutations(const_154562267411824000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154562267411826000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154562267411828000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154562267411829000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Mon Dec 24 11:37:54 CST 2018 by hengxin
