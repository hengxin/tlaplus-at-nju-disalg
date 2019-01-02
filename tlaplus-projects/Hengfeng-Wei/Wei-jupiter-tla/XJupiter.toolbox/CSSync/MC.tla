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
const_1546434703853130000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1546434703854131000 == 
{a, b}
----

\* SYMMETRY definition
symm_1546434703854132000 == 
Permutations(const_1546434703854131000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1546434703854133000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1546434703854134000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1546434703854136000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1546434703854137000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 21:11:43 CST 2019 by hengxin
