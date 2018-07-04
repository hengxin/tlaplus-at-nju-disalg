---- MODULE MC ----
EXTENDS OT, TLC

\* CONSTANT definitions @modelParameterConstants:0Char
const_1530688731139301000 == 
{"a"}
----

\* CONSTANT definitions @modelParameterConstants:1MaxPos
const_1530688731139302000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2MaxPr
const_1530688731139303000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3MaxLen
const_1530688731139304000 == 
1
----

\* Constant expression definition @modelExpressionEval
const_expr_1530688731139306000 == 
ApplyOps(<<Del1, Xform(Ins1, Del1)>>, <<>>)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1530688731139306000>>)
----

=============================================================================
\* Modification History
\* Created Wed Jul 04 15:18:51 CST 2018 by hengxin
