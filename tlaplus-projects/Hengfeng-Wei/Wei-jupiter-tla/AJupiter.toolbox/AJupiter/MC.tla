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
const_153586616974650000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_153586616974651000 == 
{a, b}
----

\* SYMMETRY definition
symm_153586616974652000 == 
Permutations(const_153586616974650000) \union Permutations(const_153586616974651000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_153586616974653000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_153586616974654000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153586616974655000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153586616974656000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153586616974657000 ==
QC
----
=============================================================================
\* Modification History
\* Created Sun Sep 02 13:29:29 CST 2018 by hengxin
