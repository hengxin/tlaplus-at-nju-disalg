---- MODULE MC ----
EXTENDS AfekSimplified, TLC

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
const_15416760322492000 == 
{v1, v2}
----

\* MV CONSTANT definitions Writers
const_15416760322493000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_15416760322494000 == 
{r1, r2}
----

\* CONSTANT definitions @modelParameterConstants:0InitRegVal
const_15416760322495000 == 
v1
----

\* CONSTANT definition @modelParameterDefinitions:2
def_ov_15416760322508000 ==
0 .. 2
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_15416760322509000 ==
\A i \in Writers: wrNum[i] < 2
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154167603225010000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154167603225011000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Thu Nov 08 19:20:32 CST 2018 by hengxin
