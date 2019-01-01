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
const_1546314864817100000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1546314864817101000 == 
{a, b}
----

\* SYMMETRY definition
symm_1546314864817102000 == 
Permutations(const_1546314864817101000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1546314864817103000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1546314864817105000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1546314864817106000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 11:54:24 CST 2019 by hengxin
