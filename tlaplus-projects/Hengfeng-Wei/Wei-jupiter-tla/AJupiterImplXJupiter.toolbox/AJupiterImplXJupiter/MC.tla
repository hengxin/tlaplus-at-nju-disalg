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
const_154616169802079000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154616169802080000 == 
{a, b}
----

\* SYMMETRY definition
symm_154616169802081000 == 
Permutations(const_154616169802080000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154616169802082000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154616169802084000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154616169802085000 ==
XJ!Spec
----
=============================================================================
\* Modification History
\* Created Sun Dec 30 17:21:38 CST 2018 by hengxin
