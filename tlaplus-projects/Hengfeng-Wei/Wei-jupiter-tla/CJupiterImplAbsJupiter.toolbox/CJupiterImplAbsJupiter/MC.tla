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
const_154514435688116000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154514435688117000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154514435688118000 == 
Permutations(const_154514435688116000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154514435688119000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154514435688120000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154514435688121000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154514435688122000 ==
AbsJ!Spec
----
=============================================================================
\* Modification History
\* Created Tue Dec 18 22:45:56 CST 2018 by hengxin
