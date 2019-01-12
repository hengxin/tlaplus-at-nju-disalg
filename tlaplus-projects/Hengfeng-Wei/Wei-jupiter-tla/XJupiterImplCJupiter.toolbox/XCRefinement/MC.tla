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
const_154729619271474000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154729619271475000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154729619271476000 == 
Permutations(const_154729619271474000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154729619271477000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154729619271478000 == 
Cop
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154729619271479000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154729619271480000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154729619271481000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Sat Jan 12 20:29:52 CST 2019 by hengxin
