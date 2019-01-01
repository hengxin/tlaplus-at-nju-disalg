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
const_154631435338572000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154631435338573000 == 
{a, b}
----

\* SYMMETRY definition
symm_154631435338574000 == 
Permutations(const_154631435338573000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154631435338575000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154631435338577000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154631435338578000 ==
QC
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 11:45:53 CST 2019 by hengxin
