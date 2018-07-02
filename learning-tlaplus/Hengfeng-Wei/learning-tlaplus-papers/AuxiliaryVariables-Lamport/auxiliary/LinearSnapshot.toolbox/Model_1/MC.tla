---- MODULE MC ----
EXTENDS LinearSnapshot, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Writers
const_1477127990133207000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1477127990143208000 == 
{r1, r2}
----

\* MV CONSTANT definitions RegVals
const_1477127990153209000 == 
{v1, v2}
----

\* CONSTANT definitions @modelParameterConstants:2InitRegVal
const_1477127990163210000 == 
v1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1477127990193213000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1477127990203214000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sat Oct 22 02:19:50 PDT 2016 by lamport
