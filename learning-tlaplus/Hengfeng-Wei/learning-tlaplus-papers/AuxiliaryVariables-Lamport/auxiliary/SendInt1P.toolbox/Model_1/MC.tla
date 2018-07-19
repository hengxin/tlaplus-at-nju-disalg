---- MODULE MC ----
EXTENDS SendInt1P, TLC

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1477127728246153000 ==
-3..3
----
\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1477127728256154000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1477127728266155000 ==
SpecP
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1477127728276156000 ==
TypeOKP
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1477127728286157000 ==
SI2!Spec
----
=============================================================================
\* Modification History
\* Created Sat Oct 22 02:15:28 PDT 2016 by lamport
