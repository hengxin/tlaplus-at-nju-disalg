---- MODULE MC ----
EXTENDS OT, TLC

\* CONSTANT definitions @modelParameterConstants:0CH
const_1505480326703317000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:1POS
const_1505480326703318000 == 
0 .. 5
----

\* CONSTANT definitions @modelParameterConstants:2LOP
const_1505480326703319000 == 
[type |-> "del", pos |-> 1, ch |-> "a", pr |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:3ROP
const_1505480326703320000 == 
[type |-> "del", pos |-> 0, ch |-> "b", pr |-> 1]
----

\* CONSTANT definitions @modelParameterConstants:4PR
const_1505480326703321000 == 
{0,1}
----

\* Constant expression definition @modelExpressionEval
const_expr_1505480326703323000 == 
Xform(LOP, ROP)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1505480326703323000>>)
----

=============================================================================
\* Modification History
\* Created Fri Sep 15 20:58:46 CST 2017 by hengxin
