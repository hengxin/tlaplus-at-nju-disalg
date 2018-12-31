---- MODULE MC ----
EXTENDS CJupiterImplAbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Char
const_154626108272630000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154626108272631000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154626108272632000 == 
Permutations(const_154626108272630000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154626108272633000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154626108272634000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154626108272635000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154626108272636000 ==
AbsJ!Spec
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 20:58:02 CST 2018 by hengxin
