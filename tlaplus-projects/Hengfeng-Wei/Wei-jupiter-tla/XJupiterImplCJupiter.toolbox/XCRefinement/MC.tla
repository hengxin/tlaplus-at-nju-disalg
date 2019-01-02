---- MODULE MC ----
EXTENDS XJupiterImplCJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Char
const_1546435010883162000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_1546435010883163000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1546435010883164000 == 
Permutations(const_1546435010883162000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_1546435010883165000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_1546435010883166000 == 
Cop
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_1546435010883167000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1546435010883168000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1546435010883169000 ==
CJ!Spec
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 21:16:50 CST 2019 by hengxin
