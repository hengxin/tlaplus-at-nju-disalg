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
const_154631462866786000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154631462866787000 == 
{a, b}
----

\* SYMMETRY definition
symm_154631462866788000 == 
Permutations(const_154631462866787000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154631462866789000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154631462866791000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154631462866792000 ==
XJ!Spec
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 11:50:28 CST 2019 by hengxin
