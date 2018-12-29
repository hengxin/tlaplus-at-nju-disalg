---- MODULE MC ----
EXTENDS XJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1545984047692212000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1545984047692213000 == 
{a, b}
----

\* SYMMETRY definition
symm_1545984047692214000 == 
Permutations(const_1545984047692213000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1545984047692215000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1545984047692217000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1545984047692218000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Fri Dec 28 16:00:47 CST 2018 by hengxin
