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
const_154631409701451000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154631409701452000 == 
{a, b}
----

\* SYMMETRY definition
symm_154631409701453000 == 
Permutations(const_154631409701452000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154631409701454000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154631409701456000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154631409701457000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 11:41:37 CST 2019 by hengxin
