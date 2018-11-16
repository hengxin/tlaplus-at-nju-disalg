---- MODULE MC ----
EXTENDS CJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154234410618915000 == 
{c1}
----

\* MV CONSTANT definitions Char
const_154234410618916000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154234410618917000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154234410618919000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154234410618920000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_154234410618921000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Fri Nov 16 12:55:06 CST 2018 by hengxin
