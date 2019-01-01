---- MODULE MC ----
EXTENDS AbsJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_15463131711959000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154631317119510000 == 
{a, b}
----

\* SYMMETRY definition
symm_154631317119511000 == 
Permutations(const_154631317119510000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154631317119512000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154631317119514000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154631317119515000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 11:26:11 CST 2019 by hengxin
