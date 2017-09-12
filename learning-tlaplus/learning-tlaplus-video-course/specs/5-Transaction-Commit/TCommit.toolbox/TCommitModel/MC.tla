---- MODULE MC ----
EXTENDS TCommit, TLC

\* CONSTANT definitions @modelParameterConstants:0RM
const_150520686658656000 == 
{"r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8"}
----

\* INIT definition @modelBehaviorInit:0
init_150520686658657000 ==
TCInit
----
\* NEXT definition @modelBehaviorNext:0
next_150520686658658000 ==
TCNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_150520686658659000 ==
TCTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_150520686658660000 ==
TCConsistent
----
=============================================================================
\* Modification History
\* Created Tue Sep 12 17:01:06 CST 2017 by hengxin
