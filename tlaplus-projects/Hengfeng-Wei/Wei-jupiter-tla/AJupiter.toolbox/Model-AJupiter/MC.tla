---- MODULE MC ----
EXTENDS AJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_15299303539582000 == 
{a, b, c}
----

\* CONSTANT definitions @modelParameterConstants:2Char
const_15299303539583000 == 
{"x", "y", "z"}
----

\* INIT definition @modelBehaviorInit:0
init_15299303539585000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_15299303539586000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15299303539587000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Mon Jun 25 20:39:13 CST 2018 by hengxin
