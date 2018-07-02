---- MODULE MC ----
EXTENDS DieHarder, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
big, small
----

\* MV CONSTANT definitions Jugs
const_146677368651475000 == 
{big, small}
----

\* CONSTANT definitions @modelParameterConstants:1Goal
const_146677368652476000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:2Capacity
const_146677368653477000 == 
(big :> 5) @@ (small :> 3)
----

\* CONSTANT definitions @modelParameterConstants:3defaultInitValue
const_146677368654478000 == 
[j \in Jugs |-> 0]
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_146677368655579000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Fri Jun 24 21:08:06 CST 2016 by hengxin
