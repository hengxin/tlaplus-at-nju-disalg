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
const_1546436152930178000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1546436152930179000 == 
{a, b}
----

\* SYMMETRY definition
symm_1546436152930180000 == 
Permutations(const_1546436152930179000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1546436152930181000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1546436152930182000 == 
AJMsg
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1546436152930184000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1546436152930185000 ==
QC
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 21:35:52 CST 2019 by hengxin
