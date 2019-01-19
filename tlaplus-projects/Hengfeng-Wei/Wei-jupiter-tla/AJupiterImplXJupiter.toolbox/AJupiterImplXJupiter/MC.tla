---- MODULE MC ----
EXTENDS AJupiterImplXJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154786649203650000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154786649203651000 == 
{a, b}
----

\* SYMMETRY definition
symm_154786649203652000 == 
Permutations(const_154786649203651000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154786649203653000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154786649203654000 == 
AJMsgEx
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154786649203656000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154786649203657000 ==
XJ!Spec
----
=============================================================================
\* Modification History
\* Created Sat Jan 19 10:54:52 CST 2019 by hengxin
