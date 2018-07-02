---- MODULE MC ----
EXTENDS SimpleAllocator, TLC

\* CONSTANT definitions @modelParameterConstants:0Clients
const_149597374823827000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:1Resources
const_149597374823828000 == 
{"r1", "r2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_149597374823829000 ==
SimpleAllocator
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_149597374823830000 ==
Safety
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_149597374823831000 ==
Liveness
----
=============================================================================
\* Modification History
\* Created Sun May 28 20:15:48 CST 2017 by ics-ant
