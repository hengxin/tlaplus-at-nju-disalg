---- MODULE MC ----
EXTENDS AbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_153787841127744000 == 
{a, b, c}
----

\* CONSTANT definitions @modelParameterConstants:1O
const_153787841127745000 == 
{<<a, 1>>, <<b,1>>, <<b,2>>, <<c,1>>, <<c,2>>}
----

\* CONSTANT definitions @modelParameterConstants:2co
const_153787841127746000 == 
a :> << <<a,1>> >> @@ b :> << <<b,1>>, <<b,2>> >> @@ c:> << <<c,1>>, <<c,2>> >>
----

\* CONSTANT definitions @modelParameterConstants:3so
const_153787841127747000 == 
<< <<a, 1>>, <<b,1>>, <<b,2>>, <<c,1>>, <<c,2>> >>
----

\* CONSTANT definitions @modelParameterConstants:4hb
const_153787841127848000 == 
{<< <<a,1>>, <<c,2>> >>, << <<b,1>>, <<c,2>> >>}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_153787841127849000 ==
1 .. 2
----
\* Constant expression definition @modelExpressionEval
const_expr_153787841127850000 == 
eo
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_153787841127850000>>)
----

=============================================================================
\* Modification History
\* Created Tue Sep 25 20:26:51 CST 2018 by hengxin
