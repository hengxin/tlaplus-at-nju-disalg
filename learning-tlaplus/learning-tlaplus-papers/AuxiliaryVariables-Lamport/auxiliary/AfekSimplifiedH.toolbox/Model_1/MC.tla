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
const_147712755784390000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_147712755784491000 == 
{r1, r2}
----

\* MV CONSTANT definitions RegVals
const_147712755785492000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_147712755786493000 == 
Permutations(const_147712755784390000)
----

\* CONSTANT definitions @modelParameterConstants:3InitRegVal
const_147712755789494000 == 
v1
----

\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_147712755792497000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_147712755793498000
----
\* CONSTANT definition @modelParameterDefinitions:4
def_ov_147712755794499000 ==
0..2
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1477127557954100000 ==
\A i \in Writers :
    wrNum[i] < 2
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1477127557964101000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1477127557974102000 ==
TypeOKH
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1477127557984103000 ==
NLS!SafeSpec
----
=============================================================================
\* Modification History
\* Created Sat Oct 22 02:12:37 PDT 2016 by lamport
