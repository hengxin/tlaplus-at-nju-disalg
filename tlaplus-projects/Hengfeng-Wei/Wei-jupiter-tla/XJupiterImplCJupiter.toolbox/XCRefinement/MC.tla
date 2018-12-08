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
const_154424230599744000 == 
{a, b, c}
----

\* MV CONSTANT definitions Client
const_154424230599745000 == 
{c1, c2, c3}
----

\* SYMMETRY definition
symm_154424230599746000 == 
Permutations(const_154424230599744000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154424230599747000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154424230599748000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154424230599749000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154424230599750000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Sat Dec 08 12:11:45 CST 2018 by hengxin
