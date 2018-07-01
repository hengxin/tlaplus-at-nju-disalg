---- MODULE MC ----
EXTENDS AJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_15304361888992000 == 
{a, b, c}
----

\* CONSTANT definitions @modelParameterConstants:2Char
const_15304361888993000 == 
{"x", "y", "z"}
----

\* CONSTANT definitions @modelParameterConstants:3Cop
const_15304361888994000 == 
[a |-> <<[type |-> "Ins", pos |-> 0, ch |-> "x", pr |-> 1], [type |-> "Del", pos |-> 0]>>, b |-> <<[type |-> "Ins", pos |-> 0, ch |-> "a", pr |-> 2]>>, c |-> <<[type |-> "Ins", pos |-> 1, ch |-> "b", pr |-> 3]>>]
----

\* INIT definition @modelBehaviorInit:0
init_15304361889006000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_15304361889007000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15304361889008000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sun Jul 01 17:09:48 CST 2018 by hengxin
