---- MODULE MC ----
EXTENDS CJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_153595464199686000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_153595464199687000 == 
{a, b}
----

\* SYMMETRY definition
symm_153595464199688000 == 
Permutations(const_153595464199686000) \union Permutations(const_153595464199687000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_153595464199689000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153595464199691000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153595464199692000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Mon Sep 03 14:04:01 CST 2018 by hengxin
