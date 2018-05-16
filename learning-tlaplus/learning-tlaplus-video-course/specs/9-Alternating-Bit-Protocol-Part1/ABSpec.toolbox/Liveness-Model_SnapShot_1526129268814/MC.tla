---- MODULE MC ----
EXTENDS ABSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f, g
----

\* MV CONSTANT definitions Data
const_152612926478387000 == 
{a, b, c, d, e, f, g}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_152612926478488000 ==
FairSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152612926478489000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_152612926478490000 ==
Inv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_152612926478491000 ==
\A v \in Data \X {0,1} : (AVar = v) ~> (BVar = v)
----
=============================================================================
\* Modification History
\* Created Sat May 12 20:47:44 CST 2018 by hengxin
