---- MODULE MC ----
EXTENDS XJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_153925998983694000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_153925998983695000 == 
{a, b}
----

\* SYMMETRY definition
symm_153925998983696000 == 
Permutations(const_153925998983694000) \union Permutations(const_153925998983695000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_153925998983697000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153925998983799000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1539259989837100000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Thu Oct 11 20:13:09 CST 2018 by hengxin
