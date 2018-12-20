---- MODULE MC ----
EXTENDS AbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_154426175640093000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154426175640094000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_154426175640095000 == 
Permutations(const_154426175640094000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154426175640096000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154426175640098000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154426175640099000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sat Dec 08 17:35:56 CST 2018 by hengxin
