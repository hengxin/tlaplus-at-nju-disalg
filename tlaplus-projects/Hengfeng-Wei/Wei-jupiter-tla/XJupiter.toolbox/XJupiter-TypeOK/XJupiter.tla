------------------------------ MODULE XJupiter ------------------------------
(*
Specification of the Jupiter protocol described in CSCW'2014 
by Yi Xu, Chengzheng Sun, and Mo Li.
We call it XJupiter, with 'X' for "Xu".
*)
EXTENDS Integers, OT, TLC, AdditionalFunctionOperators, AdditionalSequenceOperators
-----------------------------------------------------------------------------
CONSTANTS
    Client,     \* the set of client replicas
    Server,     \* the (unique) server replica
    Char,       \* set of characters allowed
    InitState   \* the initial state of each replica

Replica == Client \cup {Server}

List == Seq(Char \cup Range(InitState))   \* all possible lists/strings
MaxLen == Cardinality(Char) + Len(InitState) \* the max length of lists in any states;
    \* We assume that all inserted elements are unique.

ClientNum == Cardinality(Client)
Priority == CHOOSE f \in [Client -> 1 .. ClientNum] : Injective(f)

\* direction flags
Local == 0
Remote == 1
----------------------------------------------------------------------
ASSUME 
    /\ Range(InitState) \cap Char = {}  \* due to the uniqueness requirement
    /\ Priority \in [Client -> 1 .. ClientNum]
-----------------------------------------------------------------------------
(* 
The set of all operations.                                        
Note: The positions are indexed from 1.
*)
Rd == [type: {"Rd"}]
Del == [type: {"Del"}, pos: 1 .. MaxLen]
Ins == [type: {"Ins"}, pos: 1 .. (MaxLen + 1), ch: Char, pr: 1 .. ClientNum] \* pr: priority

Op == Ins \cup Del
-----------------------------------------------------------------------------
(* 
Cop: operation of type Op with context                            
*)
Oid == [c: Client, seq: Nat]  \* operation identifier
Cop == [op: Op \cup {Nop}, oid: Oid, ctx: SUBSET Oid]

(* 
OT of two operations of type Cop.                                 
*)
COT(lcop, rcop) == [lcop EXCEPT !.op = Xform(lcop.op, rcop.op), !.ctx = @ \cup {rcop.oid}]
-----------------------------------------------------------------------------
VARIABLES
    (* 
      For the client replicas:
    *)
    cseq,   \* cseq[c]: local sequence number at client c \in Client
    (*
     The 2D state spaces (ss, for short).
     Each client maintains one 2D state space.
     The server maintains n 2D state spaces, one for each client.
    *)
    css,    \* css[c]: the 2D state space at client c \in Client
    ccur,   \* cur[c]: the current node of css[c]
    sss,    \* sss[c]: the 2D state space maintained by the Server for client c \in Client
    scur,   \* scur[c]: the current node of sss[c]
    (* 
    For all replicas 
    *)
    state,  \* state[r]: state (the list content) of replica r \in Replica
    (* 
    For communication between the Server and the Clients:         
    *)
    cincoming,  \* cincoming[c]: incoming channel at the client c \in Client
    sincoming,  \* incoming channel at the Server
    (* 
    For model checking:                                           
    *)
    chins   \* a set of chars to insert
-----------------------------------------------------------------------------
comm == INSTANCE CSComm WITH Msg <- Cop
-----------------------------------------------------------------------------
eVars == <<chins>>  \* variables for the environment
cVars == <<cseq>>   \* variables for the clients
cssVars == <<css, ccur>>    \* variables for 2D state spaces at clients
sssVars == <<sss, scur>>    \* variables for 2D state spaces at the Server
commVars == <<cincoming, sincoming>>    \* variables for communication
vars == <<eVars, cVars, commVars, cssVars, sssVars, state>> \* all variables
-----------------------------------------------------------------------------
(* 
A 2D state space is a directed graph with labeled edges.
It is represented by a record with node field and edge field.
Each node is characterized by its context, a set of operations.
Each edge is labeled with an operation 
and a direction flag indicating whether this edge is LOCAL or REMOTE.
For clarity, we denote edges by records instead of tuples.
*)
IsSS(G) ==
    /\ G = [node |-> G.node, edge |-> G.edge]
    /\ G.node \subseteq (SUBSET Oid)
    /\ G.edge \subseteq [from: G.node, to: G.node, cop: Cop, lr: {Local, Remote}]

TypeOK == 
    (* 
      For the client replicas:
    *)
    /\ cseq \in [Client -> Nat]
    (* 
      For the 2D state spaces:
    *)
    /\ \A c \in Client: IsSS(css[c]) /\ IsSS(sss[c])
    /\ ccur \in [Client -> SUBSET Oid]
    /\ scur \in [Client -> SUBSET Oid]
    /\ state \in [Replica -> List]
    (* 
      For communication between the server and the clients:
    *)
    /\ comm!TypeOK
    (* 
      For model checking:
    *)
    /\ chins \subseteq Char
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Init predicate.                                               *)
(*********************************************************************)
Init == 
    (* 
      For the client replicas:
    *)
    /\ cseq = [c \in Client |-> 0]
    (* 
      For the 2D state spaces:
    *)
    /\ css = [c \in Client |-> [node |-> {{}}, edge |-> {}]]
    /\ ccur = [c \in Client |-> {}]
    /\ sss = [c \in Client |-> [node |-> {{}}, edge |-> {}]]
    /\ scur = [c \in Client |-> {}]
    (*
      For all replicas:
    *)
    /\ state = [r \in Replica |-> InitState]
    (* 
      For communication between the server and the clients:
    *)
    /\ comm!Init
    (* 
      For model checking:
    *)
    /\ chins = Char
-----------------------------------------------------------------------------
(* 
Locate the node in the 2D state space ss which matches the context ctx of cop.    
*)
Locate(cop, ss) == CHOOSE n \in (ss.node) : n = cop.ctx

(* 
xForm: iteratively transform cop with a path
through the 2D state space ss at some client, 
following the edges with the direction flag d.
*)
xForm(cop, ss, cur, d) ==
    LET u == Locate(cop, ss)
        v == u \cup {cop.oid}
        RECURSIVE xFormHelper(_, _, _, _)
        \* 'h' stands for "helper"; xss: eXtra ss created during transformation
        xFormHelper(uh, vh, coph, xss) ==  
            IF uh = cur
            THEN xss
            ELSE LET e == CHOOSE e \in ss.edge: e.from = uh /\ e.lr = d
                     uprime == e.to
                     copprime == e.cop
                     coph2copprime == COT(coph, copprime)
                     copprime2coph == COT(copprime, coph)
                     vprime == vh \cup {copprime.oid}
                  IN xFormHelper(uprime, vprime, coph2copprime,
                        [xss EXCEPT !.node = @ \o <<vprime>>,
                                    \* the order of recording edges here is important
                                    \* so that the last one is labeled with the final transformed operation
                                    !.edge = @ \o <<[from |-> vh, to |-> vprime, cop |-> copprime2coph, lr |-> d],
                                                    [from |-> uprime, to |-> vprime, cop |-> coph2copprime, lr |-> 1 - d]>>])  
    IN xFormHelper(u, v, cop, [node |-> <<v>>, 
                               edge |-> <<[from |-> u, to |-> v, cop |-> cop, lr |-> 1 - d]>>])
-----------------------------------------------------------------------------
(* 
Client c \in Client perform operation cop guided by the direction flag d.
*)
ClientPerform(cop, c, d) ==
    LET xss == xForm(cop, css[c], ccur[c], d)
        xn == xss.node
        xe == xss.edge
        xcur == Last(xn)
        xcop == Last(xe).cop
    IN /\ css' = [css EXCEPT ![c].node = @ \cup Range(xn),
                             ![c].edge = @ \cup Range(xe)]
       /\ ccur' = [ccur EXCEPT ![c] = xcur]
       /\ state' = [state EXCEPT ![c] = Apply(xcop.op, @)]
(* 
Client c \in Client issues an operation op.
*)
DoOp(c, op) == \* op: the raw operation generated by the client c \in Client
    /\ cseq' = [cseq EXCEPT ![c] = @ + 1]
    /\ LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq'[c]], ctx |-> ccur[c]]    
        IN /\ ClientPerform(cop, c, Remote)
           /\ comm!CSend(cop)

DoIns(c) ==
    \E ins \in Ins:
        /\ ins.pos \in 1 .. (Len(state[c]) + 1)
        /\ ins.ch \in chins
        /\ ins.pr = Priority[c]
        /\ chins' = chins \ {ins.ch} \* We assume that all inserted elements are unique.
        /\ DoOp(c, ins)
        /\ UNCHANGED <<sssVars>>

DoDel(c) == 
    \E del \in Del:
        /\ del.pos \in 1 .. Len(state[c])
        /\ DoOp(c, del)
        /\ UNCHANGED <<sssVars, eVars>>

Do(c) == 
    \/ DoIns(c)
    \/ DoDel(c)
(* 
Client c \in Client receives a message from the Server.
*)
Rev(c) == 
    /\ comm!CRev(c)
    /\ LET cop == Head(cincoming[c]) \* the received (transformed) operation
        IN ClientPerform(cop, c, Local)
    /\ UNCHANGED <<eVars, cVars, sssVars>>
-----------------------------------------------------------------------------
(*
The Server performs operation cop.
*)
ServerPerform(cop) == 
    LET c == cop.oid.c
      xss == xForm(cop, sss[c], scur[c], Remote)
       xn == xss.node
       xe == xss.edge
     xcur == Last(xn)
     xcop == Last(xe).cop 
    IN /\ sss' = [cl \in Client |-> 
                    IF cl = c 
                    THEN [sss[cl] EXCEPT !.node = @ \cup Range(xn),
                                         !.edge = @ \cup Range(xe)]
                    ELSE LET scurcl == scur[cl] 
                            scurclprime == scurcl \cup {cop.oid}
                         IN [sss[cl] EXCEPT !.node = @ \cup {scurclprime},
                                            !.edge = @ \cup {[from |-> scurcl, to |-> scurclprime, 
                                                               cop |-> xcop, lr |-> Remote]}]
                 ]
       /\ scur' = [cl \in Client |->
                    IF cl = c THEN xcur ELSE scur[cl] \cup {cop.oid}]
       /\ state' = [state EXCEPT ![Server] = Apply(xcop.op, @)]
       /\ comm!SSendSame(c, xcop)  \* broadcast the transformed operation
(* 
The Server receives a message.
*)
SRev == 
    /\ comm!SRev
    /\ LET cop == Head(sincoming)
        IN ServerPerform(cop)
    /\ UNCHANGED <<eVars, cVars, cssVars>>
-----------------------------------------------------------------------------
(* 
The next-state relation.
*)
Next == 
    \/ \E c \in Client: Do(c) \/ Rev(c)
    \/ SRev
(* 
The Spec.  (TODO: Check the fairness condition.)
*)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=============================================================================
\* Modification History
\* Last modified Wed Oct 10 15:00:09 CST 2018 by hengxin
\* Created Tue Oct 09 16:33:18 CST 2018 by hengxin