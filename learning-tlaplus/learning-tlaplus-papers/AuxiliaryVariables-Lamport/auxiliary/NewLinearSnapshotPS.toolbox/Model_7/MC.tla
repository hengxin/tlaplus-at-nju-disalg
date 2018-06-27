---- MODULE MC ----
EXTENDS NewLinearSnapshotPS, TLC

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
const_1477131585341389000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1477131585351390000 == 
{r1, r2}
----

\* MV CONSTANT definitions RegVals
const_1477131585361391000 == 
{v1, v2}
----

\* CONSTANT definitions @modelParameterConstants:3InitRegVal
const_1477131585371392000 == 
v1
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1477131585381393000 ==
0..2
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1477131585411396000 ==
\A j \in Readers : Len(rstate[j]) < 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1477131585421397000 ==
SpecP
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1477131585431398000 ==
[][\A i \in Readers : BeginRdP(i) => 
     (IF p'[i] = 1 THEN 1 ELSE 0) \in {0,1}]_varsP
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1477131585441399000 ==
[][\A i \in Writers, cmd \in RegVals :
      BeginWrP(i, cmd) => 
        {j \in Readers : (rstate[j] # << >>) 
                            /\  (p[j] = Len(rstate'[j]))}
            \in (SUBSET Readers)]_varsP
----
=============================================================================
\* Modification History
\* Created Sat Oct 22 03:19:45 PDT 2016 by lamport
