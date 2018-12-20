---- MODULE MC ----
EXTENDS XJupiterExtended, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154519102421130000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154519102421131000 == 
{a, b}
----

\* SYMMETRY definition
symm_154519102421132000 == 
Permutations(const_154519102421131000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154519102421133000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154519102421235000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154519102421236000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Wed Dec 19 11:43:44 CST 2018 by hengxin
