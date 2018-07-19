---- MODULE MC ----
EXTENDS SendSetUndoP, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2
----

\* MV CONSTANT definitions Data
const_1477127869939174000 == 
{d1, d2}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1477127869959176000 ==
SpecU
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1477127869969177000 ==
Condition
----
=============================================================================
\* Modification History
\* Created Sat Oct 22 02:17:49 PDT 2016 by lamport
