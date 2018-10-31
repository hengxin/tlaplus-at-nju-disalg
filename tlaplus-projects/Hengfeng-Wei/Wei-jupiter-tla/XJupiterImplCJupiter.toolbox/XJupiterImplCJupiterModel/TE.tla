---- MODULE TE ----
EXTENDS XJupiterImplCJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1540984104327155000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1540984104327156000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1540984104327157000 == 
<<>>
----

\* TRACE EXPLORER variable declaration @traceExploreExpressions
VARIABLES __trace_var_1540984104328160000,__trace_var_1540984104328162000
----

\* TRACE EXPLORER identifier definition @traceExploreExpressions
trace_def_1540984104328159000 ==
IgnoreDir(SetReduce((+), Range(s2ss), [node |-> {{}}, edge |-> {}]))
----

\* TRACE EXPLORER identifier definition @traceExploreExpressions
trace_def_1540984104328161000 ==
PrintT(css)
----

\* TRACE INIT definitiontraceExploreInit
init_1540984104328163000 ==
 soids = (
{}
)/\
 sincoming = (
<<>>
)/\
 s2ss = (
(c1 :> [node |-> {{}}, edge |-> {}] @@ c2 :> [node |-> {{}}, edge |-> {}])
)/\
 ccur = (
(c1 :> {} @@ c2 :> {})
)/\
 cxss = (
(c1 :> [node |-> {{}}, edge |-> {}] @@ c2 :> [node |-> {{}}, edge |-> {}])
)/\
 chins = (
{a, b}
)/\
 cseq = (
(c1 :> 0 @@ c2 :> 0)
)/\
 scur = (
(c1 :> {} @@ c2 :> {})
)/\
 cincoming = (
(c1 :> <<>> @@ c2 :> <<>>)
)/\
 c2ss = (
(c1 :> [node |-> {{}}, edge |-> {}] @@ c2 :> [node |-> {{}}, edge |-> {}])
)/\
 state = (
(c1 :> <<>> @@ c2 :> <<>> @@ Server :> <<>>)
)/\
 cincomingCJ = (
(c1 :> <<>> @@ c2 :> <<>>)
)
----

\* TRACE NEXT definitiontraceExploreNext
next_1540984104328164000 ==
( soids = (
{}
)/\
 sincoming = (
<<>>
)/\
 s2ss = (
(c1 :> [node |-> {{}}, edge |-> {}] @@ c2 :> [node |-> {{}}, edge |-> {}])
)/\
 ccur = (
(c1 :> {} @@ c2 :> {})
)/\
 cxss = (
(c1 :> [node |-> {{}}, edge |-> {}] @@ c2 :> [node |-> {{}}, edge |-> {}])
)/\
 chins = (
{a, b}
)/\
 cseq = (
(c1 :> 0 @@ c2 :> 0)
)/\
 scur = (
(c1 :> {} @@ c2 :> {})
)/\
 cincoming = (
(c1 :> <<>> @@ c2 :> <<>>)
)/\
 c2ss = (
(c1 :> [node |-> {{}}, edge |-> {}] @@ c2 :> [node |-> {{}}, edge |-> {}])
)/\
 state = (
(c1 :> <<>> @@ c2 :> <<>> @@ Server :> <<>>)
)/\
 cincomingCJ = (
(c1 :> <<>> @@ c2 :> <<>>)
)/\
 soids' = (
{}
)/\
 sincoming' = (
<< [ sctx |-> {},
     oid |-> [c |-> c1, seq |-> 1],
     op |-> [type |-> "Ins", pos |-> 1, ch |-> a, pr |-> 1],
     ctx |-> {} ] >>
)/\
 s2ss' = (
(c1 :> [node |-> {{}}, edge |-> {}] @@ c2 :> [node |-> {{}}, edge |-> {}])
)/\
 ccur' = (
(c1 :> {[c |-> c1, seq |-> 1]} @@ c2 :> {})
)/\
 cxss' = (
(c1 :> [node |-> {{}}, edge |-> {}] @@ c2 :> [node |-> {{}}, edge |-> {}])
)/\
 chins' = (
{b}
)/\
 cseq' = (
(c1 :> 1 @@ c2 :> 0)
)/\
 scur' = (
(c1 :> {} @@ c2 :> {})
)/\
 cincoming' = (
(c1 :> <<>> @@ c2 :> <<>>)
)/\
 c2ss' = (
( c1 :>
      [ node |-> {{}, {[c |-> c1, seq |-> 1]}},
        edge |->
            { [ cop |->
                    [ sctx |-> {},
                      oid |-> [c |-> c1, seq |-> 1],
                      op |-> [type |-> "Ins", pos |-> 1, ch |-> a, pr |-> 1],
                      ctx |-> {} ],
                from |-> {},
                to |-> {[c |-> c1, seq |-> 1]},
                lr |-> 0 ] } ] @@
  c2 :> [node |-> {{}}, edge |-> {}] )
)/\
 state' = (
(c1 :> <<a>> @@ c2 :> <<>> @@ Server :> <<>>)
)/\
 cincomingCJ' = (
(c1 :> <<>> @@ c2 :> <<>>)
))
\/
( soids = (
{}
)/\
 sincoming = (
<< [ sctx |-> {},
     oid |-> [c |-> c1, seq |-> 1],
     op |-> [type |-> "Ins", pos |-> 1, ch |-> a, pr |-> 1],
     ctx |-> {} ] >>
)/\
 s2ss = (
(c1 :> [node |-> {{}}, edge |-> {}] @@ c2 :> [node |-> {{}}, edge |-> {}])
)/\
 ccur = (
(c1 :> {[c |-> c1, seq |-> 1]} @@ c2 :> {})
)/\
 cxss = (
(c1 :> [node |-> {{}}, edge |-> {}] @@ c2 :> [node |-> {{}}, edge |-> {}])
)/\
 chins = (
{b}
)/\
 cseq = (
(c1 :> 1 @@ c2 :> 0)
)/\
 scur = (
(c1 :> {} @@ c2 :> {})
)/\
 cincoming = (
(c1 :> <<>> @@ c2 :> <<>>)
)/\
 c2ss = (
( c1 :>
      [ node |-> {{}, {[c |-> c1, seq |-> 1]}},
        edge |->
            { [ cop |->
                    [ sctx |-> {},
                      oid |-> [c |-> c1, seq |-> 1],
                      op |-> [type |-> "Ins", pos |-> 1, ch |-> a, pr |-> 1],
                      ctx |-> {} ],
                from |-> {},
                to |-> {[c |-> c1, seq |-> 1]},
                lr |-> 0 ] } ] @@
  c2 :> [node |-> {{}}, edge |-> {}] )
)/\
 state = (
(c1 :> <<a>> @@ c2 :> <<>> @@ Server :> <<>>)
)/\
 cincomingCJ = (
(c1 :> <<>> @@ c2 :> <<>>)
)/\
 soids' = (
{[c |-> c1, seq |-> 1]}
)/\
 sincoming' = (
<<>>
)/\
 s2ss' = (
( c1 :>
      [ node |-> {{}, {[c |-> c1, seq |-> 1]}},
        edge |->
            { [ cop |->
                    [ sctx |-> {},
                      oid |-> [c |-> c1, seq |-> 1],
                      op |-> [type |-> "Ins", pos |-> 1, ch |-> a, pr |-> 1],
                      ctx |-> {} ],
                from |-> {},
                to |-> {[c |-> c1, seq |-> 1]},
                lr |-> 0 ] } ] @@
  c2 :>
      [ node |-> {{}, {[c |-> c1, seq |-> 1]}},
        edge |->
            { [ cop |->
                    [ sctx |-> {},
                      oid |-> [c |-> c1, seq |-> 1],
                      op |-> [type |-> "Ins", pos |-> 1, ch |-> a, pr |-> 1],
                      ctx |-> {} ],
                from |-> {},
                to |-> {[c |-> c1, seq |-> 1]},
                lr |-> 1 ] } ] )
)/\
 ccur' = (
(c1 :> {[c |-> c1, seq |-> 1]} @@ c2 :> {})
)/\
 cxss' = (
( c1 :> [node |-> {{}}, edge |-> {}] @@
  c2 :>
      [ node |-> {{}, {[c |-> c1, seq |-> 1]}},
        edge |->
            { [ cop |->
                    [ sctx |-> {},
                      oid |-> [c |-> c1, seq |-> 1],
                      op |-> [type |-> "Ins", pos |-> 1, ch |-> a, pr |-> 1],
                      ctx |-> {} ],
                from |-> {},
                to |-> {[c |-> c1, seq |-> 1]},
                lr |-> 0 ] } ] )
)/\
 chins' = (
{b}
)/\
 cseq' = (
(c1 :> 1 @@ c2 :> 0)
)/\
 scur' = (
(c1 :> {[c |-> c1, seq |-> 1]} @@ c2 :> {[c |-> c1, seq |-> 1]})
)/\
 cincoming' = (
( c1 :> <<>> @@
  c2 :>
      << [ sctx |-> {},
           oid |-> [c |-> c1, seq |-> 1],
           op |-> [type |-> "Ins", pos |-> 1, ch |-> a, pr |-> 1],
           ctx |-> {} ] >> )
)/\
 c2ss' = (
( c1 :>
      [ node |-> {{}, {[c |-> c1, seq |-> 1]}},
        edge |->
            { [ cop |->
                    [ sctx |-> {},
                      oid |-> [c |-> c1, seq |-> 1],
                      op |-> [type |-> "Ins", pos |-> 1, ch |-> a, pr |-> 1],
                      ctx |-> {} ],
                from |-> {},
                to |-> {[c |-> c1, seq |-> 1]},
                lr |-> 0 ] } ] @@
  c2 :> [node |-> {{}}, edge |-> {}] )
)/\
 state' = (
(c1 :> <<a>> @@ c2 :> <<>> @@ Server :> <<a>>)
)/\
 cincomingCJ' = (
( c1 :> <<>> @@
  c2 :>
      << [ sctx |-> {},
           oid |-> [c |-> c1, seq |-> 1],
           op |-> [type |-> "Ins", pos |-> 1, ch |-> a, pr |-> 1],
           ctx |-> {} ] >> )
))
----

=============================================================================
\* Modification History
\* Created Wed Oct 31 19:08:24 CST 2018 by hengxin
