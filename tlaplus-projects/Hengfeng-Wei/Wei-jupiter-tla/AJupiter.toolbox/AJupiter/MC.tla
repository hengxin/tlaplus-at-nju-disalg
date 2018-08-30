---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_153551912797747000 == 
{"c1", "c2"}
----

\* CONSTANT definitions @modelParameterConstants:1Char
const_153551912797748000 == 
{"a","b","c","d"}
----

\* CONSTANT definitions @modelParameterConstants:2Server
const_153551912797749000 == 
"s"
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_153551912797750000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153551912797852000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153551912797853000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153551912797854000 ==
QC
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_153551912797855000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Wed Aug 29 13:05:27 CST 2018 by hengxin
