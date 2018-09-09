---- MODULE MC ----
EXTENDS CJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a
----

\* MV CONSTANT definitions Client
const_153639726723134000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Char
const_153639726723135000 == 
{a}
----

\* SYMMETRY definition
symm_153639726723136000 == 
Permutations(const_153639726723134000) \union Permutations(const_153639726723135000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_153639726723137000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153639726723139000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153639726723140000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153639726723141000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Sat Sep 08 17:01:07 CST 2018 by hengxin
