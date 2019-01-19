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
const_15477818382262000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_15477818382263000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_15477818382264000 == 
Permutations(const_15477818382262000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_15477818382265000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_15477818382266000 == 
Cop
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_15477818382277000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15477818382278000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_15477818382279000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Fri Jan 18 11:23:58 CST 2019 by hengxin
