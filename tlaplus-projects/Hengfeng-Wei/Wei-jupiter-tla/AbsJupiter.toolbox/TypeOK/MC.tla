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
const_154631369522337000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154631369522338000 == 
{a, b}
----

\* SYMMETRY definition
symm_154631369522339000 == 
Permutations(const_154631369522338000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154631369522340000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154631369522342000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154631369522343000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 11:34:55 CST 2019 by hengxin
