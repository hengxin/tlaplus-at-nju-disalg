---- MODULE MC ----
EXTENDS InsertTree, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Char
const_154494554643451000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_154494554643452000 == 
Permutations(const_154494554643451000)
----

\* CONSTANT definitions @modelParameterConstants:0Charnum
const_154494554643453000 == 
3
----

=============================================================================
\* Modification History
\* Created Sun Dec 16 15:32:26 CST 2018 by xhdn
