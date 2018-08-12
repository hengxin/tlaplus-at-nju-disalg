\* :1:__trace_var_1534045078615266000:AtoB"$!@$!@$!@$!@$!"
---- MODULE TE ----
EXTENDS AB, TLC

\* CONSTANT definitions @modelParameterConstants:0Data
const_1534045078627269000 == 
{"d1", "d2"}
----

\* TRACE EXPLORER variable declaration @traceExploreExpressions
VARIABLES __trace_var_1534045078615266000
----

\* TRACE INIT definitiontraceExploreInit
init_1534045078615267000 ==
 AtoB = (
<<>>
)/\
 BVar = (
<<"d1", 1>>
)/\
 AVar = (
<<"d1", 1>>
)/\
 BtoA = (
<<>>
)/\
__trace_var_1534045078615266000 = (
AtoB
)
----

\* TRACE NEXT definitiontraceExploreNext
next_1534045078615268000 ==
( AtoB = (
<<>>
)/\
 BVar = (
<<"d1", 1>>
)/\
 AVar = (
<<"d1", 1>>
)/\
 BtoA = (
<<>>
)/\
 AtoB' = (
<<>>
)/\
 BVar' = (
<<"d1", 1>>
)/\
 AVar' = (
<<"d1", 1>>
)/\
 BtoA' = (
<<>>
)/\
__trace_var_1534045078615266000' = (
AtoB
)')
----

\* PROPERTY definition
prop_1534045078627270000 ==
~<>[](
 AtoB = (
<<>>
)/\
 BVar = (
<<"d1", 1>>
)/\
 AVar = (
<<"d1", 1>>
)/\
 BtoA = (
<<>>
)
)
----

=============================================================================
\* Modification History
\* Created Sun Aug 12 11:37:58 CST 2018 by hengxin
