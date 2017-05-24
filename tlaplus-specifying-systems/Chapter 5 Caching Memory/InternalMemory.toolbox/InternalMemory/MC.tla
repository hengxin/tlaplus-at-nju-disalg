---- MODULE MC ----
EXTENDS InternalMemory, TLC

\* CONSTANT definitions @modelParameterConstants:0Val
const_1495612718689290000 == 
{1,2,3,4}
----

\* CONSTANT definitions @modelParameterConstants:1Proc
const_1495612718704291000 == 
{"p1", "p2", "p3"}
----

\* CONSTANT definitions @modelParameterConstants:2InitMemInt
const_1495612718704292000 == 
{0}
----

\* CONSTANT definitions @modelParameterConstants:3Adr
const_1495612718704293000 == 
{"a1", "a2", "a3"}
----

\* CONSTANT definitions @modelParameterConstants:4Send(p, d, miOld, miNew)
const_1495612718704294000(p, d, miOld, miNew) == 
/\ p \in Proc
/\ miOld \in InitMemInt
/\ miNew \in InitMemInt
/\ miNew = miOld
----

\* CONSTANT definitions @modelParameterConstants:5Reply(p, d, miOld, miNew)
const_1495612718704295000(p, d, miOld, miNew) == 
/\ p \in Proc
/\ miOld \in InitMemInt
/\ miNew \in InitMemInt
/\ miNew = miOld
----

\* INIT definition @modelBehaviorInit:0
init_1495612718704297000 ==
IInit
----
\* NEXT definition @modelBehaviorNext:0
next_1495612718704298000 ==
INext
----
=============================================================================
\* Modification History
\* Created Wed May 24 15:58:38 CST 2017 by ics-ant
