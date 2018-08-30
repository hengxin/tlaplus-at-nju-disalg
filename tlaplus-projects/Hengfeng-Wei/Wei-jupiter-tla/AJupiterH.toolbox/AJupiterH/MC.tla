---- MODULE MC ----
EXTENDS AJupiterH, TLC

\* CONSTANT definitions @modelParameterConstants:1Client
const_153563741054899000 == 
{"c1", "c2", "c3"}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1535637410549100000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:3Char
const_1535637410549101000 == 
{"a", "b"}
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_1535637410549102000
----
\* INIT definition @modelBehaviorInit:0
init_1535637410549103000 ==
InitH
----
\* NEXT definition @modelBehaviorNext:0
next_1535637410549104000 ==
NextH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1535637410549105000 ==
TypeOKH
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1535637410549106000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Thu Aug 30 21:56:50 CST 2018 by hengxin
