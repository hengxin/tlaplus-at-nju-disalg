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
const_1477131045667293000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1477131045677294000 == 
{r1, r2}
----

\* MV CONSTANT definitions RegVals
const_1477131045687295000 == 
{v1, v2}
----

\* CONSTANT definitions @modelParameterConstants:3InitRegVal
const_1477131045697296000 == 
v1
----

\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1477131045727299000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_1477131045737300000
----
\* CONSTANT definition @modelParameterDefinitions:4
def_ov_1477131045747301000 ==
0..3
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1477131045757302000 ==
\A j \in Readers : Len(rstate[j]) < 4
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1477131045767303000 ==
SpecPS
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1477131045777304000 ==
TypeOKPS
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1477131045787305000 ==
LS!Spec
----
=============================================================================
\* Modification History
\* Created Sat Oct 22 03:10:45 PDT 2016 by lamport
