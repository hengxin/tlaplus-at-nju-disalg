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
const_1477131092402320000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1477131092412321000 == 
{r1, r2}
----

\* MV CONSTANT definitions RegVals
const_1477131092422322000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_1477131092432323000 == 
Permutations(const_1477131092402320000) \union Permutations(const_1477131092412321000)
----

\* CONSTANT definitions @modelParameterConstants:3InitRegVal
const_1477131092442324000 == 
v1
----

\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1477131092472327000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_1477131092482328000
----
\* CONSTANT definition @modelParameterDefinitions:4
def_ov_1477131092492329000 ==
0..5
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1477131092502330000 ==
\A j \in Readers : Len(rstate[j]) < 6
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1477131092512331000 ==
SpecPS
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1477131092522332000 ==
TypeOKPS
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1477131092532333000 ==
LS!SafeSpec
----
=============================================================================
\* Modification History
\* Created Sat Oct 22 03:11:32 PDT 2016 by lamport
