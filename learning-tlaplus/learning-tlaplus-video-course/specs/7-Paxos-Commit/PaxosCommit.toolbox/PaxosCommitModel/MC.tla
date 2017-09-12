---- MODULE MC ----
EXTENDS PaxosCommit, TLC

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_1505223557563160000 == 
{0,1}
----

\* CONSTANT definitions @modelParameterConstants:1Acceptor
const_1505223557563161000 == 
{a1, a2, a3}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_1505223557563162000 == 
{{a1,a2},{a2,a3},{a1,a3}}
----

\* CONSTANT definitions @modelParameterConstants:3RM
const_1505223557563163000 == 
{r1,r2}
----

\* INIT definition @modelBehaviorInit:0
init_1505223557563164000 ==
PCInit
----
\* NEXT definition @modelBehaviorNext:0
next_1505223557563165000 ==
PCNext
----
=============================================================================
\* Modification History
\* Created Tue Sep 12 21:39:17 CST 2017 by hengxin
