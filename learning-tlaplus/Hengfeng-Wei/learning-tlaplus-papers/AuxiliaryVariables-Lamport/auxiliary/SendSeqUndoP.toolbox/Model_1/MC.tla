---- MODULE MC ----
EXTENDS SendSeqUndoP, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2, d3
----

\* MV CONSTANT definitions Data
const_148322935370116000 == 
{d1, d2, d3}
----

\* CONSTANT definition @modelParameterDefinitions:1
CONSTANT def_ov_148322935372218000
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_148322935373219000 ==
Len(y) < 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_148322935374320000 ==
SpecUP
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_148322935375321000 ==
TypeOKP
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_148322935376422000 ==
SS!Spec
----
=============================================================================
\* Modification History
\* Created Sat Dec 31 16:09:13 PST 2016 by lamport
