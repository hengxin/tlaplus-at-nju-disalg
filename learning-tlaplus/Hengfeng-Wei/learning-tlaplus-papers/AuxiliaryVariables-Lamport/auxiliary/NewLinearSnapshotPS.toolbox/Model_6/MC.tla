---- MODULE MC ----
EXTENDS NewLinearSnapshotPS, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3, r4
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Writers
const_1477131437852345000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1477131437862346000 == 
{r1, r2, r3, r4}
----

\* MV CONSTANT definitions RegVals
const_1477131437872347000 == 
{v1, v2}
----

\* CONSTANT definitions @modelParameterConstants:3InitRegVal
const_1477131437882348000 == 
v1
----

\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1477131437912351000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_1477131437922352000
----
\* CONSTANT definition @modelParameterDefinitions:4
def_ov_1477131437932353000 ==
0..5
----
\* INIT definition @modelBehaviorNoSpec:0
init_1477131437942354000 ==
FALSE/\interface = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1477131437952355000 ==
FALSE/\interface' = interface
----
=============================================================================
\* Modification History
\* Created Sat Oct 22 03:17:17 PDT 2016 by lamport
