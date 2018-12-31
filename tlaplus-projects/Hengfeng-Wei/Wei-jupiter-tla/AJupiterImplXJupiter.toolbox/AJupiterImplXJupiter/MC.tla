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
const_154626269689879000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154626269689880000 == 
{a, b}
----

\* SYMMETRY definition
symm_154626269689881000 == 
Permutations(const_154626269689880000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154626269689882000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154626269689884000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154626269689985000 ==
XJ!Spec
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 21:24:56 CST 2018 by hengxin
