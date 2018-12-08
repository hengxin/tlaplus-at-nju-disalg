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
const_154391901805259000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154391901805260000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154391901805261000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154391901805363000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154391901805364000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Tue Dec 04 18:23:38 CST 2018 by hengxin
