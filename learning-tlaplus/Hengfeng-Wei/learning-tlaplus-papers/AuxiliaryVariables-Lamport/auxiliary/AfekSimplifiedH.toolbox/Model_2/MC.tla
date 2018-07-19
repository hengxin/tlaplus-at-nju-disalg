---- MODULE MC ----
EXTENDS AfekSimplifiedH, TLC

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
const_147993936481155000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_147993936482156000 == 
{r1, r2}
----

\* MV CONSTANT definitions RegVals
const_147993936483157000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_147993936484158000 == 
Permutations(const_147993936481155000)
----

\* CONSTANT definitions @modelParameterConstants:3InitRegVal
const_147993936485159000 == 
v1
----

\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_147993936488162000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_147993936489163000
----
\* CONSTANT definition @modelParameterDefinitions:4
def_ov_147993936490164000 ==
0..3
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_147993936491165000 ==
\A i \in Writers :
    wrNum[i] < 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_147993936492166000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_147993936493167000 ==
TypeOKH
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_147993936494168000 ==
NLS!SafeSpec
----
=============================================================================
\* Modification History
\* Created Wed Nov 23 14:16:04 PST 2016 by lamport
