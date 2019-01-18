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
const_15476922573402000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_15476922573403000 == 
{a, b}
----

\* SYMMETRY definition
symm_15476922573404000 == 
Permutations(const_15476922573403000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_15476922573405000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_15476922573406000 == 
AJMsg
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15476922573418000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15476922573419000 ==
QC
----
=============================================================================
\* Modification History
\* Created Thu Jan 17 10:30:57 CST 2019 by hengxin
