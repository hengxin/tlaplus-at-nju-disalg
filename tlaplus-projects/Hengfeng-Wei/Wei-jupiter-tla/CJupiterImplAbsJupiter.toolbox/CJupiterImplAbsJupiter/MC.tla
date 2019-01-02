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
const_1546434214444114000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_1546434214444115000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1546434214444116000 == 
Permutations(const_1546434214444114000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_1546434214444117000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1546434214444118000 == 
Cop
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_1546434214444119000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1546434214444120000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1546434214444121000 ==
AbsJ!Spec
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 21:03:34 CST 2019 by hengxin
