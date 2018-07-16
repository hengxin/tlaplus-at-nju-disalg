---- MODULE MC ----
EXTENDS ABSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c, d, e, f, g
----

\* MV CONSTANT definitions Data
const_1526129516675117000 == 
{a, b, c, d, e, f, g}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1526129516676118000 ==
FairSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1526129516676119000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1526129516677120000 ==
Inv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1526129516677121000 ==
\A v \in Data \X {0,1} : (AVar = v) ~> (BVar = v)
----
=============================================================================
\* Modification History
\* Created Sat May 12 20:51:56 CST 2018 by hengxin
