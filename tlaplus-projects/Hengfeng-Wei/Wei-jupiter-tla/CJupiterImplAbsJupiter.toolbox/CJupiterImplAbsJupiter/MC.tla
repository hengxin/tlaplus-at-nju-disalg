---- MODULE MC ----
EXTENDS CJupiterImplAbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Char
const_1544846276141201000 == 
{a, b, c}
----

\* MV CONSTANT definitions Client
const_1544846276141202000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1544846276141203000 == 
Permutations(const_1544846276141201000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_1544846276141204000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_1544846276141205000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1544846276141206000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1544846276141207000 ==
AbsJ!Spec
----
=============================================================================
\* Modification History
\* Created Sat Dec 15 11:57:56 CST 2018 by hengxin
