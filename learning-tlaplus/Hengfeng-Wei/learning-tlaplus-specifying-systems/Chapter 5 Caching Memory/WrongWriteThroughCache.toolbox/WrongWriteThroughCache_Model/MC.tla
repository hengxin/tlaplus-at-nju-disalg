---- MODULE MC ----
EXTENDS WrongWriteThroughCache, TLC

\* CONSTANT definitions @modelParameterConstants:0InitMemInt
const_1495628227833396000 == 
{0}
----

\* CONSTANT definitions @modelParameterConstants:1Adr
const_1495628227833397000 == 
{"a1", "a2"}
----

\* CONSTANT definitions @modelParameterConstants:2QLen
const_1495628227833398000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3Val
const_1495628227833399000 == 
{1, 2}
----

\* CONSTANT definitions @modelParameterConstants:4Proc
const_1495628227833400000 == 
{"p1", "p2"}
----

\* CONSTANT definitions @modelParameterConstants:5Reply(p, d, miOld, miNew)
const_1495628227833401000(p, d, miOld, miNew) == 
/\ p \in Proc
/\ miOld \in InitMemInt
/\ miNew \in InitMemInt
/\ miNew = miOld
----

\* CONSTANT definitions @modelParameterConstants:6Send(p, d, miOld, miNew)
const_1495628227833402000(p, d, miOld, miNew) == 
/\ p \in Proc
/\ miOld \in InitMemInt
/\ miNew \in InitMemInt
/\ miNew = miOld
----

\* CONSTANT definition @modelParameterDefinitions:1
CONSTANT def_ov_1495628227833404000
----
\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1495628227833405000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_1495628227833406000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1495628227833407000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1495628227833408000 ==
Coherence
----
=============================================================================
\* Modification History
\* Created Wed May 24 20:17:07 CST 2017 by ics-ant
