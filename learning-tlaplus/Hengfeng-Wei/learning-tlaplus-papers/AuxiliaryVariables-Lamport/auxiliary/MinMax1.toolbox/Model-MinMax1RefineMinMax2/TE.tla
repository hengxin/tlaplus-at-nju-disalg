---- MODULE TE ----
EXTENDS MinMax1, TLC

\* CONSTANT definition @modelParameterDefinitions:2
CONSTANT def_ov_1540986290415234000
----
\* CONSTANT definition @modelParameterDefinitions:3
CONSTANT def_ov_1540986290415235000
----
\* CONSTANT definition @modelParameterDefinitions:4
def_ov_1540986290415236000 ==
1 .. 4
----
\* TRACE EXPLORER variable declaration @traceExploreExpressions
VARIABLES __trace_var_1540986290415238000
----

\* TRACE EXPLORER identifier definition @traceExploreExpressions
trace_def_1540986290415237000 ==
M!min
----

\* TRACE INIT definitiontraceExploreInit
init_1540986290415239000 ==
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
next_1540986290415240000 ==
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
\* Created Wed Oct 31 19:44:50 CST 2018 by hengxin
