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
const_154729735357898000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154729735357899000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1547297353578100000 == 
Permutations(const_154729735357898000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_1547297353578101000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1547297353578102000 == 
Cop
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_1547297353578103000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1547297353578104000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1547297353578105000 ==
AbsJ!Spec
----
=============================================================================
\* Modification History
\* Created Sat Jan 12 20:49:13 CST 2019 by hengxin
