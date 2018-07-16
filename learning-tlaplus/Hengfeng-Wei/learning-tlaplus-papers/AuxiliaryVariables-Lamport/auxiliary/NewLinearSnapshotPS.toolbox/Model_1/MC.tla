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
const_1477128099189254000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1477128099199255000 == 
{r1, r2}
----

\* MV CONSTANT definitions RegVals
const_1477128099209256000 == 
{v1, v2}
----

\* CONSTANT definitions @modelParameterConstants:3InitRegVal
const_1477128099219257000 == 
v1
----

\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1477128099249260000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_1477128099259261000
----
\* CONSTANT definition @modelParameterDefinitions:4
def_ov_1477128099269262000 ==
0..2
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1477128099279263000 ==
\A j \in Readers : Len(rstate[j]) < 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1477128099289264000 ==
SpecPS
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1477128099299265000 ==
TypeOKPS
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1477128099309266000 ==
LS!SafeSpec
----
=============================================================================
\* Modification History
\* Created Sat Oct 22 02:21:39 PDT 2016 by lamport
