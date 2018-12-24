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
const_154562305969851000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154562305969852000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154562305969853000 == 
Permutations(const_154562305969851000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154562305969954000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154562305969955000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154562305969956000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154562305969957000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Mon Dec 24 11:44:19 CST 2018 by hengxin
