-------------------------- MODULE SimpleAllocator --------------------------
EXTENDS FiniteSets
CONSTANTS Clients, Resources
ASSUME IsFiniteSet(Resources)
VARIABLES 
    unsat,  \* unsat[c] denotes the outstanding requests of client c
    alloc   \* alloc[c] denotes the resources allocated to client c    
-----------------------------------------------------------------------------
TypeInvariant ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]
    
available == \* Set of resources free for allocation
    Resources \ (UNION {alloc[c] : c \in Clients})
-----------------------------------------------------------------------------
Init == \* Initially, no resources have been requested or allocated
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]
Request(c, S) == \* Client c requests set S of resources
    /\ S # {} /\ unsat[c] = {} /\ alloc[c] = {}
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ UNCHANGED alloc
Allocate(c, S) == \* Set S of available resources are allocated to client c
    /\ S # {} /\ S \subseteq available \cap unsat[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = @ \ S]
Return(c, S) == \* Client c returns a set of resources that it holds
    /\ S # {} /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
    /\ UNCHANGED unsat
Next == \* The system's next-state relation
    \E c \in Clients, S \in SUBSET Resources:
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
vars == <<unsat, alloc>>                    
-----------------------------------------------------------------------------
SimpleAllocator == \* The complete high-level specification
    /\ Init /\ [] [Next]_vars
    /\ \A c \in Clients: WF_vars(Return(c, alloc[c]))
    /\ \A c \in Clients: WF_vars(\E S \in SUBSET Resources: Allocate(c, S))
-----------------------------------------------------------------------------
Safety == \A c1, c2 \in Clients: c1 # c2 => alloc[c1] \cap alloc[c2] = {}
Liveness == \A c \in Clients, r \in Resources: r \in unsat[c] ~> r \in alloc[c]
=============================================================================
\* Modification History
\* Last modified Sun May 28 20:15:41 CST 2017 by ics-ant
\* Created Sun May 28 19:44:57 CST 2017 by ics-ant
