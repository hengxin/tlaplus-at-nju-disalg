---- MODULE MC ----
EXTENDS AJupiterExtended, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1547298526280114000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1547298526281115000 == 
{a, b}
----

\* SYMMETRY definition
symm_1547298526281116000 == 
Permutations(const_1547298526281115000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1547298526281117000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1547298526281118000 == 
AJMsgEx
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1547298526281120000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1547298526281121000 ==
QC
----
=============================================================================
\* Modification History
\* Created Sat Jan 12 21:08:46 CST 2019 by hengxin
