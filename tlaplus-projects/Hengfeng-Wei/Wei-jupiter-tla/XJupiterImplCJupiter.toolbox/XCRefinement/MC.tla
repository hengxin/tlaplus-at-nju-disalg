---- MODULE MC ----
EXTENDS XJupiterImplCJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Char
const_154641111818544000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154641111818545000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154641111818546000 == 
Permutations(const_154641111818544000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154641111818547000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154641111818548000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154641111818549000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154641111818550000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 14:38:38 CST 2019 by hengxin
