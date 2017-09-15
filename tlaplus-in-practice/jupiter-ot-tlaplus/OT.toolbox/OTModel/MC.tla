---- MODULE MC ----
EXTENDS OT, TLC

\* CONSTANT definitions @modelParameterConstants:0CH
const_1505490672795577000 == 
{"a", "b", "c"}
----

\* CONSTANT definitions @modelParameterConstants:1POS
const_1505490672795578000 == 
0 .. 5
----

\* CONSTANT definitions @modelParameterConstants:2PR
const_1505490672795579000 == 
{0,1}
----

\* CONSTANT definitions @modelParameterConstants:3ROP
const_1505490672795580000 == 
[type |-> "ins", pos |-> 1, ch |-> "a", pr |-> 0]
----

\* CONSTANT definitions @modelParameterConstants:4LOPS
const_1505490672795581000 == 
<<[type |-> "ins", pos |-> 1, ch |-> "b", pr |-> 1], [type |-> "del", pos |-> 1, ch |-> "a", pr |-> 1]>>
----

\* CONSTANT definitions @modelParameterConstants:5LOP
const_1505490672795582000 == 
[type |-> "ins", pos |-> 1, ch |-> "b", pr |-> 1]
----

\* Constant expression definition @modelExpressionEval
const_expr_1505490672795584000 == 
XformOpOps(ROP, LOPS)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1505490672795584000>>)
----

=============================================================================
\* Modification History
\* Created Fri Sep 15 23:51:12 CST 2017 by hengxin
