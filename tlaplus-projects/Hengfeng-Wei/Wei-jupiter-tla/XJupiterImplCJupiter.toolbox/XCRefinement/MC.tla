---- MODULE MC ----
EXTENDS XJupiterImplCJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Char
const_1544871245405128000 == 
{a, b, c}
----

\* MV CONSTANT definitions Client
const_1544871245405129000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1544871245405130000 == 
Permutations(const_1544871245405128000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_1544871245405131000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_1544871245405132000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1544871245406133000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1544871245406134000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Sat Dec 15 18:54:05 CST 2018 by hengxin
