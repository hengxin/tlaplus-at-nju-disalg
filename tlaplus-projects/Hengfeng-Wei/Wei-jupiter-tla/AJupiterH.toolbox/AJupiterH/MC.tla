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
const_153576820269120000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_153576820269121000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_153576820269122000 == 
Permutations(const_153576820269120000) \union Permutations(const_153576820269121000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_153576820269223000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_153576820269224000
----
\* INIT definition @modelBehaviorInit:0
init_153576820269225000 ==
InitH
----
\* NEXT definition @modelBehaviorNext:0
next_153576820269226000 ==
NextH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153576820269227000 ==
TypeOKH
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153576820269228000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Sat Sep 01 10:16:42 CST 2018 by hengxin
