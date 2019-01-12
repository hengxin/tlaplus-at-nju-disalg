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
const_154701914801034000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154701914801035000 == 
{a, b}
----

\* SYMMETRY definition
symm_154701914801036000 == 
Permutations(const_154701914801035000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154701914801037000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154701914801038000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154701914801040000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154701914801041000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Wed Jan 09 15:32:28 CST 2019 by hengxin
