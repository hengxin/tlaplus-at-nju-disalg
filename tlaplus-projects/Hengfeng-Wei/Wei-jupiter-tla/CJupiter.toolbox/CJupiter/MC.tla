---- MODULE MC ----
EXTENDS CJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_153622448350346000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Char
const_153622448350347000 == 
{a, b}
----

\* SYMMETRY definition
symm_153622448350348000 == 
Permutations(const_153622448350346000) \union Permutations(const_153622448350347000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_153622448350349000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153622448350451000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153622448350452000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Thu Sep 06 17:01:23 CST 2018 by hengxin
