---- MODULE MC ----
EXTENDS PaxosCommit, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT definitions Acceptor
const_1505353702018105000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions RM
const_1505353702020106000 == 
{r1, r2}
----

\* SYMMETRY definition
symm_1505353702020107000 == 
Permutations(const_1505353702020106000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_1505353702020108000 == 
{0,1}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_1505353702020109000 == 
{{a1, a2}, {a2, a3}, {a3}}
----

\* INIT definition @modelBehaviorInit:0
init_1505353702020110000 ==
PCInit
----
\* NEXT definition @modelBehaviorNext:0
next_1505353702020111000 ==
PCNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1505353702020112000 ==
PCTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1505353702020113000 ==
TCConsistent
----
=============================================================================
\* Modification History
\* Created Thu Sep 14 09:48:22 CST 2017 by hengxin
