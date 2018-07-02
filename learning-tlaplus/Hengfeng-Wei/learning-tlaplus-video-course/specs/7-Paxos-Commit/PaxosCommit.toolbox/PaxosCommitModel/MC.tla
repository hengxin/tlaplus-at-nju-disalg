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
const_1505353841448132000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions RM
const_1505353841448133000 == 
{r1, r2}
----

\* SYMMETRY definition
symm_1505353841448134000 == 
Permutations(const_1505353841448132000) \union Permutations(const_1505353841448133000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_1505353841448135000 == 
{0,1}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_1505353841448136000 == 
{{a1, a2}, {a2, a3}, {a1, a3}}
----

\* INIT definition @modelBehaviorInit:0
init_1505353841448137000 ==
PCInit
----
\* NEXT definition @modelBehaviorNext:0
next_1505353841448138000 ==
PCNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1505353841448139000 ==
PCTypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1505353841448140000 ==
TCConsistent
----
=============================================================================
\* Modification History
\* Created Thu Sep 14 09:50:41 CST 2017 by hengxin
