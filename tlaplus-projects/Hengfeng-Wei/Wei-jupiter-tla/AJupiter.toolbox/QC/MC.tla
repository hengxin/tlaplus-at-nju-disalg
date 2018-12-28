---- MODULE MC ----
EXTENDS AJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154591375083141000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154591375083142000 == 
{a, b}
----

\* SYMMETRY definition
symm_154591375083143000 == 
Permutations(const_154591375083142000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154591375083144000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154591375083146000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154591375083147000 ==
QC
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_154591375083148000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Thu Dec 27 20:29:10 CST 2018 by hengxin
