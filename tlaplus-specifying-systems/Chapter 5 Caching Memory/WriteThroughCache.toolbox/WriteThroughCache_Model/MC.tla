---- MODULE MC ----
EXTENDS WriteThroughCache, TLC

\* CONSTANT definitions @modelParameterConstants:0InitMemInt
const_149579635446415000 == 
{0}
----

\* CONSTANT definitions @modelParameterConstants:1Adr
const_149579635446416000 == 
{"a1", "a2"}
----

\* CONSTANT definitions @modelParameterConstants:2Val
const_149579635446417000 == 
{1,2}
----

\* CONSTANT definitions @modelParameterConstants:3Proc
const_149579635446418000 == 
{"p1", "p2"}
----

\* CONSTANT definitions @modelParameterConstants:4Reply(p, d, miOld, miNew)
const_149579635446419000(p, d, miOld, miNew) == 
/\ p \in Proc
/\ miOld \in InitMemInt
/\ miNew \in InitMemInt
/\ miNew = miOld
----

\* CONSTANT definitions @modelParameterConstants:5Send(p, d, miOld, miNew)
const_149579635446420000(p, d, miOld, miNew) == 
/\ p \in Proc
/\ miOld \in InitMemInt
/\ miNew \in InitMemInt
/\ miNew = miOld
----

\* CONSTANT definitions @modelParameterConstants:6QLen
const_149579635446421000 == 
3
----

\* CONSTANT definition @modelParameterDefinitions:1
CONSTANT def_ov_149579635446423000
----
\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_149579635446424000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_149579635446425000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_149579635446426000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_149579635446427000 ==
Coherence
----
=============================================================================
\* Modification History
\* Created Fri May 26 18:59:14 CST 2017 by ics-ant
