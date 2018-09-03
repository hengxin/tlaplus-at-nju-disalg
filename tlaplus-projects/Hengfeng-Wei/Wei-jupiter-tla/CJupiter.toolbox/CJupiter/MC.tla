---- MODULE MC ----
EXTENDS CJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_153597406499623000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_153597406499624000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_153597406499625000 == 
Permutations(const_153597406499623000) \union Permutations(const_153597406499624000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_153597406499626000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153597406499628000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153597406499629000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Mon Sep 03 19:27:44 CST 2018 by hengxin
