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
const_154622583969830000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154622583969831000 == 
{a, b}
----

\* SYMMETRY definition
symm_154622583969832000 == 
Permutations(const_154622583969831000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154622583969833000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154622583969935000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154622583969936000 ==
XJ!Spec
----
=============================================================================
\* Modification History
\* Created Mon Dec 31 11:10:39 CST 2018 by hengxin
