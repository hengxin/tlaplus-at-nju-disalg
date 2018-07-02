---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_1530501098021136000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1State
const_1530501098021137000 == 
<<"a", "b", "c">>
----

\* CONSTANT definitions @modelParameterConstants:2Cop
const_1530501098021138000 == 
[c1 |-> <<Ins1>>, c2 |-> <<Ins2>>, c3 |-> <<>>]
----

\* CONSTANT definitions @modelParameterConstants:3Char
const_1530501098021139000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:4Server
const_1530501098021140000 == 
"s"
----

\* CONSTANT definition @modelParameterDefinitions:1
CONSTANT def_ov_1530501098021142000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1530501098021143000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1530501098021144000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Mon Jul 02 11:11:38 CST 2018 by hengxin
