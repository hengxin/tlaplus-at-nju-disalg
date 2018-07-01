----------------------------- MODULE AJupiterDo -----------------------------
(***************************************************************************)
(* Model checking the Jupiter protocol presented by Attiya and others.     *)
(***************************************************************************)
EXTENDS OT, TLC
-----------------------------------------------------------------------------
CONSTANTS
    Client,    \* the set of client replicas
    Server,    \* the (unique) server replica
    State,     \* the initial state of each replica
    Cop        \* Cop[c]: operations issued by the client c \in Client

ASSUME 
    /\ State \in List
    /\ Cop \in [Client -> Seq(Op)]

VARIABLES
    cop,      \* cop[c]: operations issued by the client c \in Client
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
    sincoming   \* incoming channel at the Server
-----------------------------------------------------------------------------
comm == INSTANCE CSComm
-----------------------------------------------------------------------------
cVars == <<cop, cbuf, crec, cstate>>
sVars == <<sbuf, srec, sstate>>
vars == cVars \o sVars \o comm!vars
-----------------------------------------------------------------------------
TypeOK == 
    /\ cop \in [Client -> Seq(Op)]
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    /\ cbuf \in [Client -> Seq(Op)]
    /\ crec \in [Client -> Nat]
    /\ cstate \in [Client -> List]
    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    /\ sbuf \in [Client -> Seq(Op)]
    /\ srec \in [Client -> Nat]
    /\ sstate \in [Client -> List]
    (*****************************************************************)
    (* For communication between the server and the clients:         *)
    (*****************************************************************)
    /\ comm!TypeOK
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Init predicate.                                               *)
(*********************************************************************)
Init == 
    /\ cop = Cop
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    /\ cbuf = [c \in Client |-> <<>>]
    /\ crec = [c \in Client |-> 0]
    /\ cstate = [c \in Client |-> State]
    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    /\ sbuf = [c \in Client |-> <<>>]
    /\ srec = [c \in Client |-> 0]
    /\ sstate = [c \in Client |-> State]
    (*****************************************************************)
    (* For communication between the server and the clients:         *)
    (*****************************************************************)
    /\ comm!Init
-----------------------------------------------------------------------------
(*********************************************************************)
(* Client c \in Client issues an operation op.                       *)
(*********************************************************************)
Do(c) == 
    /\ Print("Do", TRUE)
    /\ cop[c] # <<>>
    /\ LET op == Head(cop[c])
        IN /\ Print(op, TRUE)
           /\ cstate' = [cstate EXCEPT ![c] = Apply(op, @)] 
           /\ cbuf' = [cbuf EXCEPT ![c] = Append(@, op)]
           /\ comm!CSend([c |-> c, ack |-> crec[c], op |-> op])
    /\ crec' = [crec EXCEPT ![c] = 0]
    /\ cop' = [cop EXCEPT ![c] = Tail(@)]
    /\ UNCHANGED sVars
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Next state relation.                                          *)
(*********************************************************************)
Next == 
    \/ \E c \in Client: Do(c)
(*********************************************************************)
(* The Spec.                                                         *)
(*********************************************************************)
Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Sun Jul 01 20:24:48 CST 2018 by hengxin
\* Created Sun Jul 01 18:53:30 CST 2018 by hengxin
