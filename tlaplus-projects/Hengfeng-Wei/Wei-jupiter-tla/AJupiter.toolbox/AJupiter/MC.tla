---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_153408899854854000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1Char
const_153408899854855000 == 
{"a", "b"}
----

\* CONSTANT definitions @modelParameterConstants:2Server
const_153408899854856000 == 
"s"
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_153408899854857000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Priority
const_153408899854858000 == 
[c1 |-> 1, c2 |-> 2, c3 |-> 3]
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_153408899854960000 ==
0 .. 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153408899854961000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153408899854962000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153408899854963000 ==
QC
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_153408899854964000 ==
WLSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_153408899854965000 ==
<> comm!EmptyChannel
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_153408899854966000 ==
<> Termination
----
=============================================================================
\* Modification History
\* Created Sun Aug 12 23:49:58 CST 2018 by hengxin
