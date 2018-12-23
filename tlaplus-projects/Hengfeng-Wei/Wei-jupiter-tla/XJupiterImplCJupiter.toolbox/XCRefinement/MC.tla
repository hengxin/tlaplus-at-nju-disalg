---- MODULE MC ----
EXTENDS XJupiterImplCJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT definitions Char
const_154538923419216000 == 
{a, b, c}
----

\* MV CONSTANT definitions Client
const_154538923419217000 == 
{c1, c2, c3}
----

\* SYMMETRY definition
symm_154538923419218000 == 
Permutations(const_154538923419216000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154538923419219000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154538923419320000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154538923419321000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154538923419322000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Fri Dec 21 18:47:14 CST 2018 by hengxin
