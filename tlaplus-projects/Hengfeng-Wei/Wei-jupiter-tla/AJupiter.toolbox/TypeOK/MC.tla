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
const_1545991611239256000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1545991611239257000 == 
{a, b}
----

\* SYMMETRY definition
symm_1545991611239258000 == 
Permutations(const_1545991611239257000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1545991611239259000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1545991611239261000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1545991611239262000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Fri Dec 28 18:06:51 CST 2018 by hengxin
