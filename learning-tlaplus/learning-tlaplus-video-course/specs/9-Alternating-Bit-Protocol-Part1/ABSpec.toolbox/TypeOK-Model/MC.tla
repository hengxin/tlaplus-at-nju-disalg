---- MODULE MC ----
EXTENDS ABSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f, g
----

\* MV CONSTANT definitions Data
const_152612869349853000 == 
{a, b, c, d, e, f, g}
----

\* SYMMETRY definition
symm_152612869349854000 == 
Permutations(const_152612869349853000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_152612869349855000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152612869349856000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_152612869349857000 ==
Inv
----
=============================================================================
\* Modification History
\* Created Sat May 12 20:38:13 CST 2018 by hengxin
