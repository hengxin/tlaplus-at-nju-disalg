---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_1534083903980459000 == 
{"c1", "c2"}
----

\* CONSTANT definitions @modelParameterConstants:1Char
const_1534083903980460000 == 
{"a"}
----

\* CONSTANT definitions @modelParameterConstants:2Server
const_1534083903980461000 == 
"s"
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_1534083903980462000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Priority
const_1534083903980463000 == 
[c1 |-> 1, c2 |-> 2]
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1534083903980465000 ==
0 .. 2
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534083903980466000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534083903980467000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534083903980468000 ==
QC
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1534083903980469000 ==
<> comm!EmptyChannel
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1534083903980470000 ==
<> Termination
----
=============================================================================
\* Modification History
\* Created Sun Aug 12 22:25:03 CST 2018 by hengxin
