---- MODULE MC ----
EXTENDS AJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_153646054481472000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_153646054481473000 == 
{a, b}
----

\* SYMMETRY definition
symm_153646054481474000 == 
Permutations(const_153646054481472000) \union Permutations(const_153646054481473000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_153646054481475000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153646054481477000 ==
SpecH
----
=============================================================================
\* Modification History
\* Created Sun Sep 09 10:35:44 CST 2018 by hengxin
