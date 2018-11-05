------------------------------ MODULE CJupiter ------------------------------
(***************************************************************************)
(* Model of our own CJupiter protocol.                                     *)
(***************************************************************************)

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
----------------------------------------------------------------------
ASSUME 
    /\ Range(InitState) \cap Char = {}  \* due to the uniqueness requirement
    /\ Priority \in [Client -> 1 .. ClientNum]
-----------------------------------------------------------------------------
(*********************************************************************)
(* The set of all operations.                                        *)
(* Note: The positions are indexed from 1. *)
(*********************************************************************)
Rd == [type: {"Rd"}]
Del == [type: {"Del"}, pos: 1 .. MaxLen]
Ins == [type: {"Ins"}, pos: 1 .. (MaxLen + 1), ch: Char, pr: 1 .. ClientNum] \* pr: priority

Op == Ins \cup Del
-----------------------------------------------------------------------------
(*********************************************************************)
(* Cop: operation of type Op with context                            *)
(*********************************************************************)
Oid == [c: Client, seq: Nat]  \* operation identifier
Cop == [op: Op \cup {Nop}, oid: Oid, ctx: SUBSET Oid]
    
(*********************************************************************)
(* OT of two operations of type Cop.                                 *)
(*********************************************************************)
COT(lcop, rcop) == [lcop EXCEPT !.op = Xform(lcop.op, rcop.op), !.ctx = @ \cup {rcop.oid}]
-----------------------------------------------------------------------------
VARIABLES
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    cseq,    \* cseq[c]: local sequence number at client c \in Client
    (*
    For edge ordering
    *)
    serial, \* serial[r]: the serial order of operations from the view of each replica r \in Replica
    cincomingSerial,
    sincomingSerial,
    (*****************************************************************)
    (* For all replicas: the n-ary ordered state space               *)
    (*****************************************************************)
    css,    \* css[r]: the n-ary ordered state space at replica r \in Replica
    cur,    \* cur[r]: the current node of css at replica r \in Replica
    state,  \* state[r]: state (the list content) of replica r \in Replica
    (*****************************************************************)
    (* For communication between the Server and the Clients:         *)
    (*****************************************************************)
    cincoming,  \* cincoming[c]: incoming channel at the client c \in Client
    sincoming,  \* incoming channel at the Server
    (*****************************************************************)
    (* For model checking:                                           *)
    (*****************************************************************)
    chins   \* a set of chars to insert

(* 
tb: Is cop1 totally ordered before cop2?
This is determined according to "serial" at replica r \in Replica
*)
tb(cop1, cop2, r) == 
    LET pos1 == FirstIndexOfElementSafe(serial[r], cop1.oid)
        pos2 == FirstIndexOfElementSafe(serial[r], cop2.oid)
     IN IF pos1 # 0 /\ pos2 # 0
        THEN pos1 < pos2
        ELSE pos1 # 0
-----------------------------------------------------------------------------
comm == INSTANCE CSComm WITH Msg <- Cop
commSerial == INSTANCE CSComm 
                WITH Msg <- Seq(Oid), cincoming <- cincomingSerial, sincoming <- sincomingSerial
-----------------------------------------------------------------------------
eVars == <<chins>>  \* variables for the environment
cVars == <<cseq>>   \* variables for the clients
dsVars == <<css, cur, state>>           \* variables for the data structure: the n-ary ordered state space
commVars == <<cincoming, sincoming>>    \* variables for communication
serialVars == <<serial, cincomingSerial, sincomingSerial>>
vars == <<eVars, cVars, commVars, serialVars, dsVars>> \* all variables
-----------------------------------------------------------------------------
(*****************************************************************)
(* An css is a directed graph with labeled edges.                *)
(*                                                               *)
(* It is represented by a record with node field and edge field. *)
(*                                                               *)
(* Each node is characterized by its context, a set of operations. *)
(*                                                               *)
(* Each edge is labeled with an operation.                       *)
(* For clarity, we denote edges by records instead of tuples.    *)
(*****************************************************************)
IsCSS(G) ==
    /\ G = [node |-> G.node, edge |-> G.edge]
    /\ G.node \subseteq (SUBSET Oid)
    /\ G.edge \subseteq [from: G.node, to: G.node, cop: Cop]

TypeOK == 
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    /\ cseq \in [Client -> Nat]
    (*
    For edge ordering:
    *)
\*    /\ serial \in [Replica -> Seq(Seq(Oid))]
\*    /\ commSerial!TypeOK
    (*****************************************************************)
    (* For all replicas: the n-ary ordered state space                                      *)
    (*****************************************************************)
    /\ \A r \in Replica: IsCSS(css[r])
    /\ cur \in [Replica -> SUBSET Oid]
    /\ state \in [Replica -> List]
    (*****************************************************************)
    (* For communication between the server and the clients:         *)
    (*****************************************************************)
    /\ comm!TypeOK
    (*****************************************************************)
    (* For model checking:                                           *)
    (*****************************************************************)
    /\ chins \subseteq Char
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Init predicate.                                               *)
(*********************************************************************)
Init == 
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    /\ cseq = [c \in Client |-> 0]
    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    /\ serial = [r \in Replica |-> <<>>]
    /\ commSerial!Init
    (*****************************************************************)
    (* For all replicas: the n-ary ordered state space                                      *)
    (*****************************************************************)
    /\ css = [r \in Replica |-> [node |-> {{}}, edge |-> {}]]
    /\ cur = [r \in Replica |-> {}]
    /\ state = [r \in Replica |-> InitState]
    (*****************************************************************)
    (* For communication between the server and the clients:         *)
    (*****************************************************************)
    /\ comm!Init
    (*****************************************************************)
    (* For model checking:                                           *)
    (*****************************************************************)
    /\ chins = Char
-----------------------------------------------------------------------------
(*********************************************************************)
(* Locate the node in rcss which matches the context ctx of cop.     *)
(*                                                                   *)
(* rcss: the css at replica r \in Replica                            *)
(*********************************************************************)
Locate(cop, rcss) == CHOOSE n \in (rcss.node) : n = cop.ctx

(*********************************************************************)
(* xForm: iteratively transform cop with a path                      *)
(* through the css at replica r \in Replica, following the first edges. *)
(*********************************************************************)
xForm(cop, r) ==
    LET rcss == css[r]
        u == Locate(cop, rcss)
        v == u \cup {cop.oid}
        RECURSIVE xFormHelper(_, _, _, _)
        \* 'h' stands for "helper"; xcss: eXtra css created during transformation
        xFormHelper(uh, vh, coph, xcss) ==  
            IF uh = cur[r]
            THEN xcss
            ELSE LET fedge == CHOOSE e \in rcss.edge: 
                                /\ e.from = uh
                                /\ \A uhe \in rcss.edge: 
                                    (uhe.from = uh /\ uhe # e) => tb(e.cop, uhe.cop, r)
                     uprime == fedge.to
                     fcop == fedge.cop
                     coph2fcop == COT(coph, fcop)
                     fcop2coph == COT(fcop, coph)
                     vprime == vh \cup {fcop.oid}
                  IN xFormHelper(uprime, vprime, coph2fcop,
                        [xcss EXCEPT !.node = @ \o <<vprime>>,
                                     \* the order of recording edges here is important
                                     !.edge = @ \o <<[from |-> vh, to |-> vprime, cop |-> fcop2coph],
                                                     [from |-> uprime, to |-> vprime, cop |-> coph2fcop]>>])  
    IN xFormHelper(u, v, cop, [node |-> <<v>>, 
                               edge |-> <<[from |-> u, to |-> v, cop |-> cop]>>])

(*********************************************************************)
(* Perform cop at replica r \in Replica.                             *)
(*********************************************************************)
Perform(cop, r) ==
    LET xcss == xForm(cop, r)
        xn == xcss.node
        xe == xcss.edge
        xcur == Last(xn)
        xcop == Last(xe).cop
    IN /\ css' = [css EXCEPT ![r].node = @ \cup Range(xn),
                             ![r].edge = @ \cup Range(xe)]
       /\ cur' = [cur EXCEPT ![r] = xcur]
       /\ state' = [state EXCEPT ![r] = Apply(xcop.op, @)]
-----------------------------------------------------------------------------
(*********************************************************************)
(* Client c \in Client issues an operation op.                       *)
(*********************************************************************)
DoOp(c, op) == \* op: the raw operation generated by the client c \in Client
    /\ cseq' = [cseq EXCEPT ![c] = @ + 1]
    /\ LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq'[c]], ctx |-> cur[c]]
        IN /\ Perform(cop, c)
           /\ comm!CSend(cop)

DoIns(c) ==
    \E ins \in Ins:
        /\ ins.pos \in 1 .. (Len(state[c]) + 1)
        /\ ins.ch \in chins
        /\ ins.pr = Priority[c]
        /\ chins' = chins \ {ins.ch} \* We assume that all inserted elements are unique.
        /\ DoOp(c, ins)
        /\ UNCHANGED <<serialVars>>

DoDel(c) == 
    \E del \in Del:
        /\ del.pos \in 1 .. Len(state[c])
        /\ DoOp(c, del)
        /\ UNCHANGED <<eVars, serialVars>>

Do(c) == 
    \/ DoIns(c)
    \/ DoDel(c)
(*********************************************************************)
(* Client c \in Client receives a message from the Server.           *)
(*********************************************************************)
Rev(c) == 
    /\ comm!CRev(c)
    /\ LET cop == Head(cincoming[c]) \* the received original operation
        IN Perform(cop, c)
    /\ commSerial!CRev(c)
    /\ serial' = [serial EXCEPT ![c] = Head(cincomingSerial[c])]
    /\ UNCHANGED <<eVars, cVars>>
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Server receives a message.                                    *)
(*********************************************************************)
SRev == 
    /\ comm!SRev
    /\ LET cop == Head(sincoming)
        IN /\ Perform(cop, Server)
           /\ comm!SSendSame(cop.oid.c, cop)  \* broadcast the original operation
           /\ serial' = [serial EXCEPT ![Server] = Append(@, cop.oid)]
           /\ commSerial!SSendSame(cop.oid.c, serial')
    /\ UNCHANGED <<eVars, cVars, sincomingSerial>>
-----------------------------------------------------------------------------
(*********************************************************************)
(* The next-state relation.                                          *)
(*********************************************************************)
Next == 
    \/ \E c \in Client: Do(c) \/ Rev(c)
    \/ SRev
(*
The Spec.
There is no requirement that the clients ever generate operations.
*)
Spec == Init /\ [][Next]_vars /\ WF_vars(SRev \/ \E c \in Client: Rev(c))
-----------------------------------------------------------------------------
(*********************************************************************)
(* The compactness of CJupiter:                                      *)
(* the css at all replicas are essentially the same.               *)
(*********************************************************************)
Compactness == 
    comm!EmptyChannel => Cardinality({css[r] : r \in Replica}) = 1

THEOREM Spec => Compactness
=============================================================================
\* Modification History
\* Last modified Mon Nov 05 21:24:49 CST 2018 by hengxin
\* Created Sat Sep 01 11:08:00 CST 2018 by hengxin