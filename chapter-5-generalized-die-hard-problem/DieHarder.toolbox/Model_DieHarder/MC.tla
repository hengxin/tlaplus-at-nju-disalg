---- MODULE MC ----
EXTENDS DieHarder, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
big, small
----

\* MV CONSTANT definitions Jugs
const_1466513479167176000 == 
{big, small}
----

\* CONSTANT definitions @modelParameterConstants:1Goal
const_1466513479177177000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:2Capacity
const_1466513479187178000 == 
(big :> 5) @@ (small :> 3)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1466513479197179000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1466513479207180000 ==
\A j \in Jugs : injug[j] # Goal
----
=============================================================================
\* Modification History
\* Created Tue Jun 21 20:51:19 CST 2016 by hengxin
