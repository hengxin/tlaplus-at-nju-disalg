------------------------------ MODULE AJupiter ------------------------------
(***************************************************************************)
(* Model checking the Jupiter protocol presented by Attiya and others.     *)
(***************************************************************************)
EXTENDS OT
-----------------------------------------------------------------------------
CONSTANTS
    Client,    \* the set of client replicas
    Server     \* the (unique) server replica
    
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
    sincoming   \* incoming channel at the Server
-----------------------------------------------------------------------------
cVars == <<cbuf, crec, cstate>>
sVars == <<sbuf, srec, sstate>>
commVars == <<cincoming, sincoming>>
vars == cVars \o sVars \o commVars
-----------------------------------------------------------------------------
(***************************************************************************)
(* Messages between the Server and the Clients.                            *)
(* There are two kinds of messages according to their destinations.        *)
(***************************************************************************)
Msg ==  [c: Client, ack: Nat, op: Op] \* messages sent to the Server from a client c \in Client
       \cup [ack: Nat, op: Op] \* messages broadcast to Clients from the Server
-----------------------------------------------------------------------------
TypeOK == 
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
    /\ cincoming \in [Client -> Seq(Msg)]
    /\ sincoming \in Seq(Msg)
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Init predicate.                                               *)
(*********************************************************************)
Init == 
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    /\ cbuf = [c \in Client |-> <<>>]
    /\ crec = [c \in Client |-> 0]
    /\ cstate = [c \in Client |-> <<>>]
    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    /\ sbuf = [c \in Client |-> <<>>]
    /\ srec = [c \in Client |-> 0]
    /\ sstate = [c \in Client |-> <<>>]
    (*****************************************************************)
    (* For communication between the server and the clients:         *)
    (*****************************************************************)
    /\ cincoming = [c \in Client |-> <<>>]
    /\ sincoming = <<>>
-----------------------------------------------------------------------------
(*********************************************************************)
(* A client sends a message msg to the Server.                       *)
(*********************************************************************)
CSend(msg) == /\ sincoming' = Append(sincoming, msg)
-----------------------------------------------------------------------------
(*********************************************************************)
(* Client c \in Client generates and performs an operation op.       *)
(*********************************************************************)
Do(c, op) == 
    /\ TRUE    \* no pre-condition
    /\ cstate' = [cstate EXCEPT ![c] = Apply(op, @)]
    /\ cbuf' = [cbuf EXCEPT ![c] = Append(@, op)]
    /\ CSend([c |-> c, ack |-> crec[c], op |-> op])
    /\ crec' = [crec EXCEPT ![c] = 0]
    /\ UNCHANGED (sVars \o <<cincoming>>)
-----------------------------------------------------------------------------
(*********************************************************************)
(* Client c \in Client receives a message from the Server.           *)
(*********************************************************************)
CRev(c) == 
    /\ cincoming[c] # <<>>   \* there are messages to handle with
    /\ crec' = [crec EXCEPT ![c] = @ + 1]
    /\ LET m == Head(cincoming[c]) 
           cBuf == cbuf[c]  \* the buffer at client c \in Client
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf))  \* buffer shifted
           xop == XformOpOps(m.op, cShiftedBuf) \* transform op vs. shifted buffer
           xcBuf == XformOpsOp(cShiftedBuf, m.op) \* transform shifted buffer vs. op
        IN /\ cbuf' = [cbuf EXCEPT ![c] = xcBuf]
           /\ cstate' = [cstate EXCEPT ![c] = Apply(xop, @)] \* apply the transformed operation xop
    /\ cincoming' = [cincoming EXCEPT ![c] = Tail(@)]
    /\ UNCHANGED (sVars \o <<sincoming>>)
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Server receives a message.                                    *)
(*********************************************************************)
SRev == 
    /\ sincoming # <<>>    \* there are messages for the Server to handle with
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
           /\ cincoming' = [cl \in Client |->
                            IF cl = c
                            THEN cincoming[cl]
                            \* broadcast the transformed operation to clients other than c \in Client
                            ELSE Append(cincoming[cl], [ack |-> srec[cl], op |-> xop])] 
           /\ sstate' = Apply(xop, sstate)  \* apply the transformed operation
    /\ sincoming' = Tail(sincoming) \* consume a message
    /\ UNCHANGED cVars
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Next state relation.                                          *)
(*********************************************************************)
Next == 
    \/ \E c \in Client, op \in Op: Do(c, op)
    \/ \E c \in Client: CRev(c)
    \/ SRev
(*********************************************************************)
(* The Spec.                                                         *)
(*********************************************************************)
Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Sun Jun 24 22:26:35 CST 2018 by hengxin
\* Created Sat Jun 23 17:14:18 CST 2018 by hengxin
