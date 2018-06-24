------------------------------ MODULE AJupiter ------------------------------

(***************************************************************************)
(* Model checking the Jupiter protocol presented by Attiya and others.     *)
(***************************************************************************)

EXTENDS Op
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

(*********************************************************************)
(* The Server broadcast a message msg to the Clients                 *)
(* other than c \in Client.                                          *)
(*********************************************************************)
SBoradcast(c, msg) == 
    /\ cincoming' = [cl \in Client |->
                        IF cl = c
                        THEN cincoming[cl]
                        ELSE Append(cincoming[cl], msg)]
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
(* Client c \in Client receives a message msg from the Server.       *)
(*********************************************************************)
CRev(c, msg) == 
    /\ cincoming[c] # <<>>   \* there are messages to handle with
    /\ crec' = [crec EXCEPT ![c] = @ + 1]
    /\ LET m == Head(cincoming[c]) 
        IN /\ cbuf' = [cbuf EXCEPT ![c] = SubSeq(@, m.ack + 1, Len(@))]
           /\ cincoming' = [cincoming EXCEPT ![c] = Tail(@)]
    /\ FALSE \* TODO: (buf, o) = xform(buf, o)
    \* /\ cstate' = [cstate EXCEPT ![c] = Apply(m.op, @)] \* using o above
    /\ UNCHANGED (sVars \o <<sincoming>>)
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Server receives a message msg.                                *)
(*********************************************************************)
SRev(msg) == 
    /\ sincoming # <<>>    \* there are messages for the Server to handle with
    /\ LET m == Head(sincoming) \* the message to handle with
           c == m.c             \* the client c \in Client that sends this message
           cBuf == sbuf[c]      \* the buffer at the Server for client c \in Client
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf))
           (xop, xcBuf) == xForm(m.op, cShiftedBuf)
        IN /\ srec' = [cl \in Client |-> 
                            IF cl = c
                            THEN srec[cl] + 1
                            ELSE 0]
           /\ sbuf' = [cl \in Client |->
                            IF cl = c
                            THEN xcBuf
                            ELSE Append(sbuf[cl], xop)]
    /\ sincoming' = Tail(sincoming)
    /\ FALSE \* TODO: (o, buf[c]) = xform(o, buf[c])
    \* /\ sstate' = Apply(m.op, sstate) \* using o above
    /\ FALSE \* for all other clients
    /\ UNCHANGED cVars
-----------------------------------------------------------------------------
(*********************************************************************)
(* The next state relation.                                          *)
(*********************************************************************)
Next == FALSE
=============================================================================
\* Modification History
\* Last modified Sun Jun 24 15:44:36 CST 2018 by hengxin
\* Created Sat Jun 23 17:14:18 CST 2018 by hengxin
