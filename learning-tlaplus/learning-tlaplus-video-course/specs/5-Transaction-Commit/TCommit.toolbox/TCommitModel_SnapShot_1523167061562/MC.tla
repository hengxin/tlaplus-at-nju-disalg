---- MODULE MC ----
EXTENDS TCommit, TLC

\* CONSTANT definitions @modelParameterConstants:0RM
const_15231670562042000 == 
{"r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8"}
----

\* INIT definition @modelBehaviorInit:0
init_15231670562043000 ==
TCInit
----
\* NEXT definition @modelBehaviorNext:0
next_15231670562044000 ==
TCNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15231670562045000 ==
TCTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_15231670562046000 ==
TCConsistent
----
=============================================================================
\* Modification History
\* Created Sun Apr 08 13:57:36 CST 2018 by hengxin
