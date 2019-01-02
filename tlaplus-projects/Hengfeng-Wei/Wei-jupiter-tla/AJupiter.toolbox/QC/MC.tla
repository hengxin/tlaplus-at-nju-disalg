---- MODULE MC ----
EXTENDS AJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_15464105228539000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154641052285310000 == 
{a, b}
----

\* SYMMETRY definition
symm_154641052285311000 == 
Permutations(const_154641052285310000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154641052285312000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154641052285314000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154641052285315000 ==
QC
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 14:28:42 CST 2019 by hengxin
