---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_1531020959337330000 == 
{"c1", "c2"}
----

\* CONSTANT definitions @modelParameterConstants:1Char
const_1531020959337331000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:2Server
const_1531020959337332000 == 
"s"
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_1531020959337333000 == 
<<"a">>
----

\* CONSTANT definitions @modelParameterConstants:4Priority
const_1531020959337334000 == 
[c1 |-> 1, c2 |-> 2]
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1531020959337336000 ==
0 .. 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1531020959337337000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1531020959337338000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1531020959337339000 ==
QC
----
=============================================================================
\* Modification History
\* Created Sun Jul 08 11:35:59 CST 2018 by hengxin
