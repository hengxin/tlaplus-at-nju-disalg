---- MODULE MC ----
EXTENDS SendSeqUndoP, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2, d3
----

\* MV CONSTANT definitions Data
const_148322942110828000 == 
{d1, d2, d3}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_148322942112930000 ==
Len(y) < 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_148322942113931000 ==
SpecU
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_148322942115032000 ==
[][Condition]_vars
----
=============================================================================
\* Modification History
\* Created Sat Dec 31 16:10:21 PST 2016 by lamport
