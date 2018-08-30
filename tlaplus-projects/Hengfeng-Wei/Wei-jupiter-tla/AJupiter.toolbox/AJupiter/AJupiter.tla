------------------------------ MODULE AJupiter ------------------------------
(***************************************************************************)
(* Model checking the Jupiter protocol presented by Attiya and others.     *)
(***************************************************************************)

EXTENDS Integers, OT, TLC, AdditionalFunctionOperators
-----------------------------------------------------------------------------
CONSTANTS
    Client,     \* the set of client replicas
    Server,     \* the (unique) server replica
    Char,       \* set of characters allowed
    InitState   \* the initial state of each replica

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

Op == Ins \cup Del  \* Now we don't consider Rd operations.
-----------------------------------------------------------------------------
VARIABLES
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    cbuf,    \* cbuf[c]: buffer (of operations) at the client c \in Client
    crec,    \* crec[c]: the number of new messages have been received by the client c \in Client
                    \* since the last time a message was sent
    cstate,  \* cstate[c]: state (the list content) of the client c \in Client

    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    sbuf,    \* sbuf[c]: buffer (of operations) at the Server, one per client c \in Client
    srec,    \* srec[c]: the number of new messages have been ..., one per client c \in Client
    sstate,  \* sstate: state (the list content) of the server Server

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
comm == INSTANCE CSComm
-----------------------------------------------------------------------------
eVars == <<chins>>                      \* variables for the environment
cVars == <<cbuf, crec, cstate>>         \* variables for the clients
ecVars == <<eVars, cVars>>              \* variables for the clients and the environment
sVars == <<sbuf, srec, sstate>>         \* variables for the server
commVars == <<cincoming, sincoming>>    \* variables for communication
vars == <<eVars, cVars, sVars, commVars>> \* all variables
-----------------------------------------------------------------------------
TypeOK == 
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    /\ cbuf \in [Client -> Seq(Op \cup {Nop})]
    /\ crec \in [Client -> Int]
    /\ cstate \in [Client -> List]
    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    /\ sbuf \in [Client -> Seq(Op \cup {Nop})]
    /\ srec \in [Client -> Int]
    /\ sstate \in List
    (*****************************************************************)
    (* For communication between the server and the clients:         *)
    (*****************************************************************)
    /\ comm!TypeOK
    (*****************************************************************)
    (* For model checking:                                           *)
    (*****************************************************************)
    /\ chins \in SUBSET Char
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Init predicate.                                               *)
(*********************************************************************)
Init == 
    /\ chins = Char
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    /\ cbuf = [c \in Client |-> <<>>]
    /\ crec = [c \in Client |-> 0]
    /\ cstate = [c \in Client |-> InitState]
    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    /\ sbuf = [c \in Client |-> <<>>]
    /\ srec = [c \in Client |-> 0]
    /\ sstate = InitState
    (*****************************************************************)
    (* For communication between the server and the clients:         *)
    (*****************************************************************)
    /\ comm!Init
-----------------------------------------------------------------------------
(*********************************************************************)
(* Client c \in Client issues an operation op.                       *)
(*********************************************************************)
DoOp(c, op) == 
    /\ cstate' = [cstate EXCEPT ![c] = Apply(op, @)] 
    /\ cbuf' = [cbuf EXCEPT ![c] = Append(@, op)]
    /\ crec' = [crec EXCEPT ![c] = 0]
    /\ comm!CSend([c |-> c, ack |-> crec[c], op |-> op])

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
(* Client c \in Client receives a message from the Server.           *)
(*********************************************************************)
Rev(c) == 
    /\ comm!CRev(c)
    /\ crec' = [crec EXCEPT ![c] = @ + 1]
    /\ LET m == Head(cincoming[c]) 
           cBuf == cbuf[c]  \* the buffer at client c \in Client
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf))  \* buffer shifted
           xop == XformOpOps(m.op, cShiftedBuf) \* transform op vs. shifted buffer
           xcBuf == XformOpsOp(cShiftedBuf, m.op) \* transform shifted buffer vs. op
        IN /\ cbuf' = [cbuf EXCEPT ![c] = xcBuf]
           /\ cstate' = [cstate EXCEPT ![c] = Apply(xop, @)] \* apply the transformed operation xop
    /\ UNCHANGED <<sVars, eVars>>
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Server receives a message.                                    *)
(*********************************************************************)
SRev == 
    /\ comm!SRev
    /\ LET m == Head(sincoming) \* the message to handle with
           c == m.c             \* the client c \in Client that sends this message
           cBuf == sbuf[c]      \* the buffer at the Server for client c \in Client
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf)) \* buffer shifted
           xop == XformOpOps(m.op, cShiftedBuf) \* transform op vs. shifted buffer
           xcBuf == XformOpsOp(cShiftedBuf, m.op) \* transform shifted buffer vs. op
        IN /\ srec' = [cl \in Client |-> 
                            IF cl = c
                            THEN srec[cl] + 1 \* receive one more operation from client c \in Client
                            ELSE 0] \* reset srec for other clients than c \in Client
           /\ sbuf' = [cl \in Client |->
                            IF cl = c
                            THEN xcBuf  \* transformed buffer for client c \in Client
                            ELSE Append(sbuf[cl], xop)] \* store transformed xop into other clients' bufs
           /\ sstate' = Apply(xop, sstate)  \* apply the transformed operation
           /\ comm!SSend(c, srec, xop)
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
-----------------------------------------------------------------------------
(*********************************************************************)
(* The safety properties to check: Eventual Convergence (EC),        *)
(* Quiescent Consistency (QC), Strong Eventual Convergence (SEC),    *)
(* Weak List Specification, (WLSpec),                                *)
(* and Strong List Specification, (SLSpec).                          *)
(*********************************************************************)

(*********************************************************************)
(* Eventual Consistency (EC)                                         *)
(*********************************************************************)

(*********************************************************************)
(* Quiescent Consistency (QC)                                        *)
(*********************************************************************)
QConvergence == \forall c \in Client: cstate[c] = sstate
QC == comm!EmptyChannel => QConvergence

THEOREM Spec => []QC

(*********************************************************************)
(* Strong Eventual Consistency (SEC)                                 *)
(*********************************************************************)
=============================================================================
\* Modification History
\* Last modified Thu Aug 30 21:44:10 CST 2018 by hengxin
\* Created Sat Jun 23 17:14:18 CST 2018 by hengxin