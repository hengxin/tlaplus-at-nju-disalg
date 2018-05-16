---- MODULE MC ----
EXTENDS ABSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f, g
----

\* MV CONSTANT definitions Data
const_152612927833697000 == 
{a, b, c, d, e, f, g}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_152612927833698000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152612927833699000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1526129278336100000 ==
Inv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1526129278336101000 ==
\A v \in Data \X {0,1} : (AVar = v) ~> (BVar = v)
----
=============================================================================
\* Modification History
\* Created Sat May 12 20:47:58 CST 2018 by hengxin
