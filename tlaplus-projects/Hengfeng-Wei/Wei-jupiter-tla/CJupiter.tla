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
    /\ Range(InitState) \cap Char = {}
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
(*                                         *)
(*  *)
(*********************************************************************)
Oid == [c: Client, seq: Nat]  \* operation identifier
Cop == [op: Op \cup {Nop}, oid: Oid, ctx: SUBSET Oid, sctx: SUBSET Oid] \* operation with context

cop1 \prec cop2 == 
    \/ cop2.sctx = {}
    \/ cop1.oid \in cop2.sctx
    
COT(lcop, rcop) == 
    [op |-> Xform(lcop.op, rcop.op), oid |-> lcop.oid, 
        ctx |-> lcop.ctx \cup {rcop.oid}, sctx |-> lcop.sctx]
-----------------------------------------------------------------------------
VARIABLES
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    cseq,    \* cseq[c]: local sequence number at client c \in Client
    cstate,  \* cstate[c]: state (the list content) of the client c \in Client
    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    soids,  \* the set of operations the Server has executed
    sstate, \* sstate: state (the list content) of the server Server
    (*****************************************************************)
    (* For all replicas: the n-ary ordered state space                                      *)
    (*****************************************************************)
    css,    \* css[r]: the n-ary ordered state space at replica r \in Replica
    cur,    \* cur[r]: the current node of css at replica r \in Replica
    (*****************************************************************)
    (* For communication between the Server and the Clients:         *)
    (*****************************************************************)
    cincoming,  \* cincoming[c]: incoming channel at the client c \in Client
    sincoming,  \* incoming channel at the Server
    (*****************************************************************)
    (* For model checking:                                           *)
    (*****************************************************************)
    chins   \* a set of chars to insert

-----------------------------------------------------------------------------
comm == INSTANCE CSComm WITH Msg <- Cop
-----------------------------------------------------------------------------
eVars == <<chins>>           \* variables for the environment
cVars == <<cseq, cstate>>    \* variables for the clients
ecVars == <<eVars, cVars>>   \* variables for the clients and the environment
sVars  == <<soids, sstate>>  \* variables for the server
dsVars == <<css, cur>>       \* variables for the data structure: the n-ary ordered state space
commVars == <<cincoming, sincoming>>    \* variables for communication
vars == <<eVars, cVars, sVars, commVars, dsVars>> \* all variables
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
    /\ cstate \in [Client -> List]
    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    /\ soids \subseteq Oid
    /\ sstate \in List
    (*****************************************************************)
    (* For all replicas: the n-ary ordered state space                                      *)
    (*****************************************************************)
    /\ \A r \in Replica: IsCSS(css[r])
    /\ cur \in [Replica -> SUBSET Oid]
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
    /\ chins = Char
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    /\ cseq = [c \in Client |-> 0]
    /\ cstate = [c \in Client |-> InitState]
    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    /\ soids = {}
    /\ sstate = InitState
    (*****************************************************************)
    (* For all replicas: the n-ary ordered state space                                      *)
    (*****************************************************************)
    /\ css = [r \in Replica |-> [node |-> {{}}, edge |-> {}]]
    /\ cur = [r \in Replica |-> {}]
    (*****************************************************************)
    (* For communication between the server and the clients:         *)
    (*****************************************************************)
    /\ comm!Init
-----------------------------------------------------------------------------
(*********************************************************************)
(* Client c \in Client issues an operation op.                       *)
(*********************************************************************)
DoOp(c, op) == \* op: the raw operation generated by the client c \in Client
    /\ cstate' = [cstate EXCEPT ![c] = Apply(op, @)] 
    /\ cseq' = [cseq EXCEPT ![c] = @ + 1]
    /\ LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq'[c]],
        ctx |-> cur[c], sctx |-> {}]    \* cop: original operation with context
            v == cur[c] \cup {cop.oid}
        IN /\ css' = [css EXCEPT ![c].node = @ \cup {v},
                                 ![c].edge = @ \cup {[from |-> cur[c], to |-> v, cop |-> cop]}]
           /\ cur' = [cur EXCEPT ![c] = v]
           /\ comm!CSend(cop)

DoIns(c) ==
    \E ins \in Ins:
        /\ ins.pos \in 1 .. (Len(cstate[c]) + 1)
        /\ ins.ch \in chins
        /\ ins.pr = Priority[c]
        /\ chins' = chins \ {ins.ch} \* We assume that all inserted elements are unique.
        /\ DoOp(c, ins)
        /\ UNCHANGED sVars

DoDel(c) == 
    \E del \in Del:
        /\ del.pos \in 1 .. Len(cstate[c])
        /\ DoOp(c, del)
        /\ UNCHANGED <<sVars, eVars>>

Do(c) == 
    \/ DoIns(c)
    \/ DoDel(c)
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
                                    (uhe.from = uh /\ uhe # e) => (e.cop \prec uhe.cop)
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
    IN xFormHelper(u, v, cop, [node |-> <<v>>, edge |-> <<[from |-> u, to |-> v, cop |-> cop]>>])

(*********************************************************************)
(* The eXtra css (xcss) updates the status of replica r \in Replica. *)
(*********************************************************************)
r (+) xcss == 
    LET xn == xcss.node
        xe == xcss.edge
        xcur == Last(xn)
        xcop == Last(xe).cop
    IN /\ css' = [css EXCEPT ![r].node = @ \cup Range(xn),
                             ![r].edge = @ \cup Range(xe)]
       /\ cur' = [cur EXCEPT ![r] = xcur]
\*       /\ cstate' = [cstate EXCEPT ![r] = Apply(xcop.op, @)]
    
(*********************************************************************)
(* Client c \in Client receives a message from the Server.           *)
(*********************************************************************)
Rev(c) == 
    /\ comm!CRev(c)
    /\ LET cop == Head(cincoming[c]) \* the received original operation
          xcss == xForm(cop, c)      \* the eXtra part of css
        IN /\ c (+) xcss
           /\ cstate' = [cstate EXCEPT ![c] = Apply(Last(xcss.edge).cop.op, @)]
    /\ UNCHANGED <<cseq, sVars, eVars>>
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Server receives a message.                                    *)
(*********************************************************************)
SRev == 
    /\ comm!SRev
    /\ LET org == Head(sincoming) \* the received operation
           cop == [org EXCEPT !.sctx = soids]   \* set its sctx field
          xcss == xForm(cop, Server)    \* the eXtra part of css
        IN /\ soids' = soids \cup {cop.oid}
           /\ Server (+) xcss
           /\ sstate' = Apply(Last(xcss.edge).cop.op, sstate)  \* apply the transformed operation
           /\ comm!SSendSame(cop.oid.c, cop)  \* broadcast the original operation
    /\ UNCHANGED ecVars
-----------------------------------------------------------------------------
(*********************************************************************)
(* The next-state relation.                                          *)
(*********************************************************************)
Next == 
    \/ \E c \in Client: Do(c) \/ Rev(c)
    \/ SRev
(*********************************************************************)
(* The Spec.  (TODO: Check the fairness condition.)                  *)
(*********************************************************************)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=============================================================================
\* Modification History
\* Last modified Tue Sep 04 23:22:46 CST 2018 by hengxin
\* Created Sat Sep 01 11:08:00 CST 2018 by hengxin