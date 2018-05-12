---- MODULE MC ----
EXTENDS ABSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f, g
----

\* MV CONSTANT definitions Data
const_152612890052270000 == 
{a, b, c, d, e, f, g}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_152612890052271000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152612890052272000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_152612890052273000 ==
Inv
----
=============================================================================
\* Modification History
\* Created Sat May 12 20:41:40 CST 2018 by hengxin
