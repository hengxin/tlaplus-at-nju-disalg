---- MODULE MC ----
EXTENDS XJupiterExtended, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154156994536636000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154156994536737000 == 
{a, b}
----

\* SYMMETRY definition
symm_154156994536738000 == 
Permutations(const_154156994536636000) \union Permutations(const_154156994536737000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154156994536739000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154156994536741000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154156994536742000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Wed Nov 07 13:52:25 CST 2018 by hengxin
