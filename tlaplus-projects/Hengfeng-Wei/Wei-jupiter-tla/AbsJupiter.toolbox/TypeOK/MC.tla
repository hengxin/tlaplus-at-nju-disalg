---- MODULE MC ----
EXTENDS AbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154425150224565000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154425150224566000 == 
{a, b}
----

\* SYMMETRY definition
symm_154425150224567000 == 
Permutations(const_154425150224566000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154425150224568000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154425150224670000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154425150224671000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sat Dec 08 14:45:02 CST 2018 by hengxin
