---- MODULE MC ----
EXTENDS NewLinearSnapshotPS, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
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
const_1476167326481264000 == 
{w1, w2, w3}
----

\* MV CONSTANT definitions Readers
const_1476167326491265000 == 
{r1, r2}
----

\* MV CONSTANT definitions RegVals
const_1476167326501266000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1476167326511267000 == 
Permutations(const_1476167326481264000) \union Permutations(const_1476167326491265000)
----

\* CONSTANT definitions @modelParameterConstants:3InitRegVal
const_1476167326521268000 == 
v1
----

\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1476167326551271000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_1476167326561272000
----
\* CONSTANT definition @modelParameterDefinitions:4
def_ov_1476167326571273000 ==
0..5
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1476167326581274000 ==
\A j \in Readers : Len(rstate[j]) < 6
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1476167326591275000 ==
SpecPS
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1476167326601276000 ==
TypeOKPS
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1476167326611277000 ==
LS!SafeSpec
----
=============================================================================
\* Modification History
\* Created Mon Oct 10 23:28:46 PDT 2016 by lamport
