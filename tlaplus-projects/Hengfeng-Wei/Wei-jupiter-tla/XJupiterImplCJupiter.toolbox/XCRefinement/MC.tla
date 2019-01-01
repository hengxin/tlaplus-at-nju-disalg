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
const_154631421922065000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154631421922066000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154631421922067000 == 
Permutations(const_154631421922065000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154631421922068000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154631421922069000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154631421922070000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154631421922071000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 11:43:39 CST 2019 by hengxin
