----------------------------- MODULE JupiterOT -----------------------------
EXTENDS Naturals, FiniteSets, Sequences
CONSTANTS NumOfClients, NumOfOps
Clients == (1 .. NumOfClients)
Ops == (1 .. NumOfOps)
VARIABLE buffer \* buffer[c] stores the operations to be broadcast issued by client c 
VARIABLES 
    op,         \* Operation in the original or transformed form
    vertex,     \* Vertex of the state space graph
    edge,       \* Edge of the state space graph
    stateGraph  \* The state space graph
-----------------------------------------------------------------------------
OP == [type : {"Ins", "Del"}, pos : Nat, priority : Clients]
Vertices == SUBSET Ops
Edges == [elbl : OP, dest : Vertices]

TypeInvariant ==
    \* Ignoring "Read" operations for now
    /\ op \in OP
    \* A vertex in the state space graph represents the set of operations it has processed 
    /\ vertex \in Vertices
    /\ edge \in Edges
-----------------------------------------------------------------------------
Init ==
    /\ FALSE
Issue(c, o) == \* Client c issues an operation
    /\ c \in Clients
    /\ o 
=============================================================================
\* Modification History
\* Last modified Sat Jun 03 19:24:10 CST 2017 by ics-ant
\* Created Wed May 31 11:13:18 CST 2017 by ics-ant

\* Specification of the Jupiter protocol described in the papers
\* "High-Latency, Low-Bandwidth Windowing in the Jupiter Collaboration System" 
\* (UIST 1995) and "Achieving Convergence in Operational Transformation: 
\* Conditions, Mechanisms, and Systems" (CSCW 2014).
