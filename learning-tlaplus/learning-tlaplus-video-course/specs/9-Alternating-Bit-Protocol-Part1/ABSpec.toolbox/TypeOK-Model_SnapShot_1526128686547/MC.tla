---- MODULE MC ----
EXTENDS ABSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f, g
----

\* MV CONSTANT definitions Data
const_152612867951948000 == 
{a, b, c, d, e, f, g}
----

\* SYMMETRY definition
symm_152612867951949000 == 
Permutations(const_152612867951948000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_152612867951950000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152612867952051000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_152612867952052000 ==
Inv
----
=============================================================================
\* Modification History
\* Created Sat May 12 20:37:59 CST 2018 by hengxin
