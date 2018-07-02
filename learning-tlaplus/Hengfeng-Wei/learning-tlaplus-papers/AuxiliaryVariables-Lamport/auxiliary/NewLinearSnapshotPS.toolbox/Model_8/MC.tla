---- MODULE MC ----
EXTENDS NewLinearSnapshotPS, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Writers
const_1477131588693410000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1477131588703411000 == 
{r1, r2}
----

\* MV CONSTANT definitions RegVals
const_1477131588713412000 == 
{v1, v2}
----

\* CONSTANT definitions @modelParameterConstants:3InitRegVal
const_1477131588723413000 == 
v1
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1477131588733414000 ==
0..2
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1477131588763417000 ==
\A j \in Readers : Len(rstate[j]) < 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1477131588773418000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1477131588783419000 ==
Condition
----
=============================================================================
\* Modification History
\* Created Sat Oct 22 03:19:48 PDT 2016 by lamport
