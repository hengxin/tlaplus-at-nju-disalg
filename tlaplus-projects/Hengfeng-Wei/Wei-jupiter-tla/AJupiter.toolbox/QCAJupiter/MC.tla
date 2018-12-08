---- MODULE MC ----
EXTENDS AJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154391931927478000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154391931927479000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154391931927480000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154391931927582000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154391931927583000 ==
QC
----
=============================================================================
\* Modification History
\* Created Tue Dec 04 18:28:39 CST 2018 by hengxin
