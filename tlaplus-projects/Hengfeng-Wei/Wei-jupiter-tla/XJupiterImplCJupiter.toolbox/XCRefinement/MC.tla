---- MODULE MC ----
EXTENDS XJupiterImplCJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3, c4
----

\* MV CONSTANT definitions Char
const_154479261129996000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154479261129997000 == 
{c1, c2, c3, c4}
----

\* SYMMETRY definition
symm_154479261129998000 == 
Permutations(const_154479261129996000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154479261129999000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_1544792611300100000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1544792611300101000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1544792611300102000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Fri Dec 14 21:03:31 CST 2018 by hengxin
