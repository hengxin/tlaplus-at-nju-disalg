---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_153433294334654000 == 
{"c1", "c2"}
----

\* CONSTANT definitions @modelParameterConstants:1Char
const_153433294334655000 == 
{"a","b", "c", "d"}
----

\* CONSTANT definitions @modelParameterConstants:2Server
const_153433294334656000 == 
"s"
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_153433294334657000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Priority
const_153433294334658000 == 
[c1 |-> 1, c2 |-> 2]
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_153433294334660000 ==
0 .. 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153433294334661000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153433294334662000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153433294334663000 ==
QC
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_153433294334664000 ==
WLSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_153433294334665000 ==
<> comm!EmptyChannel
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_153433294334666000 ==
<> Termination
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 19:35:43 CST 2018 by hengxin
