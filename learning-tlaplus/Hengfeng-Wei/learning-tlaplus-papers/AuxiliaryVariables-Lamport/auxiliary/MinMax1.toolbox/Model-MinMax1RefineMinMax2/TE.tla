---- MODULE TE ----
EXTENDS MinMax1, TLC

\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1540988705861261000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_1540988705861262000
----
\* CONSTANT definition @modelParameterDefinitions:4
def_ov_1540988705861263000 ==
1 .. 4
----
\* TRACE EXPLORER variable declaration @traceExploreExpressions
VARIABLES __trace_var_1540988705861265000
----

\* TRACE EXPLORER identifier definition @traceExploreExpressions
trace_def_1540988705861264000 ==
min
----

\* TRACE INIT definitiontraceExploreInit
init_1540988705861266000 ==
 x = (
None
)/\
 y = (
{}
)/\
 turn = (
"input"
)
----

\* TRACE NEXT definitiontraceExploreNext
next_1540988705861267000 ==
( x = (
None
)/\
 y = (
{}
)/\
 turn = (
"input"
)/\
 x' = (
2
)/\
 y' = (
{}
)/\
 turn' = (
"output"
))
\/
( x = (
2
)/\
 y = (
{}
)/\
 turn = (
"output"
)/\
 x' = (
Both
)/\
 y' = (
{2}
)/\
 turn' = (
"input"
))
----

=============================================================================
\* Modification History
\* Created Wed Oct 31 20:25:05 CST 2018 by hengxin
