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
const_1547298200605106000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1547298200605107000 == 
{a, b}
----

\* SYMMETRY definition
symm_1547298200605108000 == 
Permutations(const_1547298200605107000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1547298200605109000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1547298200605110000 == 
AJMsg
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1547298200605112000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1547298200605113000 ==
QC
----
=============================================================================
\* Modification History
\* Created Sat Jan 12 21:03:20 CST 2019 by hengxin
