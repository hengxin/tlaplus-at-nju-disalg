---- MODULE MC ----
EXTENDS TCommit, TLC

\* CONSTANT definitions @modelParameterConstants:0RM
const_152316716423017000 == 
{"r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8", "r9", "r10"}
----

\* INIT definition @modelBehaviorInit:0
init_152316716423018000 ==
TCInit
----
\* NEXT definition @modelBehaviorNext:0
next_152316716423019000 ==
TCNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_152316716423020000 ==
TCTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_152316716423021000 ==
TCConsistent
----
=============================================================================
\* Modification History
\* Created Sun Apr 08 13:59:24 CST 2018 by hengxin
