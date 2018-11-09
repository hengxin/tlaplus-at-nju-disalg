---- MODULE MC ----
EXTENDS NewLinearSnapshot, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT definitions RegVals
const_15416811325592000 == 
{v1, v2}
----

\* MV CONSTANT definitions Writers
const_15416811325593000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_15416811325604000 == 
{r1, r2}
----

\* CONSTANT definitions @modelParameterConstants:0InitRegVal
const_15416811325605000 == 
v1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15416811325608000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15416811325609000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Thu Nov 08 20:45:32 CST 2018 by hengxin
