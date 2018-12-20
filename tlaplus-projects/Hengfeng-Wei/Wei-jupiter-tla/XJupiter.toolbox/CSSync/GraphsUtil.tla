----------------------------- MODULE GraphsUtil -----------------------------
(*
A module that defines graphs and the operations on them.
*)
-----------------------------------------------------------------------------
(*
A graph is a pair consisting of a set of nodes
and a set of directed edges, each of which is a pair of nodes.
It is represented by a record with node field and edge field. 
*)
IsGraph(G) ==
    /\ G = [node |-> G.node, edge |-> G.edge] 

EmptyGraph == [node |-> {{}}, edge |-> {}]

g (+) h == \* A union (in terms of set) of two graphs g and h.
    [node |-> g.node \cup h.node, edge |-> g.edge \cup h.edge]
=============================================================================
\* Modification History
\* Last modified Wed Dec 19 18:22:46 CST 2018 by hengxin
\* Created Wed Dec 19 11:11:25 CST 2018 by hengxin