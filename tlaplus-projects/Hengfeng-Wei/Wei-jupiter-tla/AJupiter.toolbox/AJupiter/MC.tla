---- MODULE MC ----
EXTENDS AJupiter, TLC

\* CONSTANT definitions @modelParameterConstants:0Client
const_1534558425137215000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1Char
const_1534558425137216000 == 
{"a","b","c"}
----

\* CONSTANT definitions @modelParameterConstants:2Server
const_1534558425137217000 == 
"s"
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_1534558425137218000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Priority
const_1534558425137219000 == 
[c1 |-> 1, c2 |-> 2, c3 |-> 3]
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_1534558425138221000 ==
0 .. 3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534558425138222000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534558425138223000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534558425138224000 ==
QC
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1534558425138225000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Sat Aug 18 10:13:45 CST 2018 by hengxin
