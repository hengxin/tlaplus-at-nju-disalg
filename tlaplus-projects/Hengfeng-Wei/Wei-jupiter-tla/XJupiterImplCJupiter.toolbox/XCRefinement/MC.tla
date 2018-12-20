---- MODULE MC ----
EXTENDS XJupiterImplCJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT definitions Char
const_154519116121637000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154519116121638000 == 
{c1, c2, c3}
----

\* SYMMETRY definition
symm_154519116121639000 == 
Permutations(const_154519116121637000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154519116121640000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154519116121641000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154519116121642000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154519116121643000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Wed Dec 19 11:46:01 CST 2018 by hengxin
