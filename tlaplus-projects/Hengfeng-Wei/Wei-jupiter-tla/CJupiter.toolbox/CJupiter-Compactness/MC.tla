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
const_154186116639660000 == 
{c1}
----

\* MV CONSTANT definitions Char
const_154186116639661000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154186116639662000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154186116639664000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154186116639665000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_154186116639666000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Sat Nov 10 22:46:06 CST 2018 by hengxin
