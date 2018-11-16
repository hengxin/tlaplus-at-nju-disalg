---- MODULE MC ----
EXTENDS CJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1542350905261122000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1542350905261123000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1542350905261124000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1542350905261126000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1542350905261127000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1542350905261128000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 14:48:25 CST 2018 by hengxin
