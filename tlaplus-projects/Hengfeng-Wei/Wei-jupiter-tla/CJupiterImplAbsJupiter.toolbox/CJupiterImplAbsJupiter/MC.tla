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
const_154631476353493000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154631476353494000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154631476353495000 == 
Permutations(const_154631476353493000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154631476353496000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154631476353497000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154631476353498000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154631476353499000 ==
AbsJ!Spec
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 11:52:43 CST 2019 by hengxin
