---- MODULE MC ----
EXTENDS InternalMemory, TLC

\* CONSTANT definitions @modelParameterConstants:0Val
const_1495799414040259000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1Proc
const_1495799414040260000 == 
{"p1", "p2", "p3"}
----

\* CONSTANT definitions @modelParameterConstants:2InitMemInt
const_1495799414040261000 == 
{0}
----

\* CONSTANT definitions @modelParameterConstants:3Adr
const_1495799414040262000 == 
{"a1", "a2", "a3"}
----

\* CONSTANT definitions @modelParameterConstants:4Send(p, d, miOld, miNew)
const_1495799414040263000(p, d, miOld, miNew) == 
/\ p \in Proc
/\ miOld \in InitMemInt
/\ miNew \in InitMemInt
/\ miNew = miOld
----

\* CONSTANT definitions @modelParameterConstants:5Reply(p, d, miOld, miNew)
const_1495799414040264000(p, d, miOld, miNew) == 
/\ p \in Proc
/\ miOld \in InitMemInt
/\ miNew \in InitMemInt
/\ miNew = miOld
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1495799414040266000 ==
ISpec
----
=============================================================================
\* Modification History
\* Created Fri May 26 19:50:14 CST 2017 by ics-ant
