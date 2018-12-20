----------------------------- MODULE StateSpace -----------------------------
(*
The graph representation of n-ary ordered state spaces and 2D state spaces
used in CJupiter and XJupiter, respectively.  
*)
EXTENDS JupiterCtx, GraphsUtil
-----------------------------------------------------------------------------
(* 
A state space is a directed graph with labeled edges.
Each node is characterized by its context, a set of operations.
Each edge is labeled with an operation.
*)
IsSS(G) ==
    /\ IsGraph(G)
    /\ G.node \subseteq (SUBSET Oid)
    /\ G.edge \subseteq [from: G.node, to: G.node, cop: Cop]

EmptySS == EmptyGraph

(*
Locate the node in a state space that matches the context ctx of cop.     
*)
Locate(cop, ss) == CHOOSE n \in ss.node : n = cop.ctx
=============================================================================
\* Modification History
\* Last modified Wed Dec 19 18:35:13 CST 2018 by hengxin
\* Created Wed Dec 19 18:15:25 CST 2018 by hengxin