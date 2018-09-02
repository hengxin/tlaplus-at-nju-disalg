---- MODULE MC ----
EXTENDS AJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_15358682079772000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_15358682079773000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_15358682079774000 == 
Permutations(const_15358682079772000) \union Permutations(const_15358682079773000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_15358682079775000 == 
<<>>
----

\* INIT definition @modelBehaviorInit:0
init_15358682079787000 ==
InitH
----
\* NEXT definition @modelBehaviorNext:0
next_15358682079788000 ==
NextH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15358682079789000 ==
TypeOKH
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153586820797810000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Sun Sep 02 14:03:27 CST 2018 by hengxin
