---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_153563721402760000 == 
{"c1", "c2"}
----

\* CONSTANT definitions @modelParameterConstants:1Char
const_153563721402761000 == 
{"a", "b"}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_153563721402762000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_153563721402763000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153563721402764000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153563721402765000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153563721402766000 ==
QC
----
=============================================================================
\* Modification History
\* Created Thu Aug 30 21:53:34 CST 2018 by hengxin
