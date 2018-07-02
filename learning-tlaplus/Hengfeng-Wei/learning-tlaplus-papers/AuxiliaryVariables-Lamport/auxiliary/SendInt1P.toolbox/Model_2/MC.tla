---- MODULE MC ----
EXTENDS SendInt1P, TLC

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1477127719612137000 ==
-3..3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1477127719622138000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1477127719632139000 ==
[][Send => \E i \in Pi : PredSend(i)]_x
----
=============================================================================
\* Modification History
\* Created Sat Oct 22 02:15:19 PDT 2016 by lamport
