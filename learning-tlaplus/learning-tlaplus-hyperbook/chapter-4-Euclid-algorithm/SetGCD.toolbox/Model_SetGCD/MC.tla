---- MODULE MC ----
EXTENDS SetGCD, TLC

\* CONSTANT definitions @modelParameterConstants:0Input
const_1466422443947134000 == 
{ 20, 55, 25, 30, 40 }
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1466422443957135000 ==
1 .. 1000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1466422443968136000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1466422443978137000 ==
PartialCorrectness
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1466422443988138000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Mon Jun 20 19:34:03 CST 2016 by hengxin
