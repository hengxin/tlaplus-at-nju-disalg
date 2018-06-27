---- MODULE MC ----
EXTENDS SendSetUndoP, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2
----

\* MV CONSTANT definitions Data
const_1477127815492164000 == 
{d1, d2}
----

\* CONSTANT definition @modelParameterDefinitions:1
CONSTANT def_ov_1477127815512166000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1477127815522167000 ==
SpecUP
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1477127815532168000 ==
TypeOKP
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1477127815542169000 ==
SS!Spec
----
=============================================================================
\* Modification History
\* Created Sat Oct 22 02:16:55 PDT 2016 by lamport
