---- MODULE MC ----
EXTENDS Poker, TLC

\* CONSTANT definitions @modelParameterConstants:0NumberOfPlayers
const_153466483426140000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1InitCard
const_153466483426141000 == 
(1 :> (1 :> 1 @@ 2 :> 1 @@ 4 :> 2 @@ 5 :> 2 @@ 7 :> 2) @@ 2 :> (3 :> 2 @@ 6 :> 2))
----

\* CONSTANT definitions @modelParameterConstants:2MaxDuplicate
const_153466483426242000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3MaxFace
const_153466483426243000 == 
7
----

\* Constant expression definition @modelExpressionEval
const_expr_153466483426244000 == 
Hand
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_153466483426244000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153466483426245000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153466483426246000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153466483426247000 ==
~Win
----
=============================================================================
\* Modification History
\* Created Sun Aug 19 15:47:14 CST 2018 by hengxin
