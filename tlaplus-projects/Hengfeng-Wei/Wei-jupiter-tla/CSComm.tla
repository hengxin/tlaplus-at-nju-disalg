------------------------------- MODULE CSComm -------------------------------
(***************************************************************************)
(* Specification of communication in a Client-Server system model.         *)
(***************************************************************************)
EXTENDS Naturals, Op

CONSTANTS
    Client,    \* the set of clients
    Server     \* the (unique) server

VARIABLES
    cincoming,  \* cincoming[c]: incoming channel at the client c \in Client
    sincoming   \* incoming channel at the Server
-----------------------------------------------------------------------------
(***************************************************************************)
(* Messages between the Server and the Clients.                            *)
(* There are two kinds of messages according to their destinations.        *)
(* TODO: Abstraction from the concrete representation of messages.         *)
(***************************************************************************)
Msg == [c: Client, ack: Nat, op: Op] \cup \* messages sent to the Server from a client c \in Client
       [ack: Nat, op: Op] \* messages broadcast to Clients from the Server
-----------------------------------------------------------------------------
TypeOK == /\ cincoming \in [Client -> Seq(Msg)]
          /\ sincoming \in Seq(Msg)
-----------------------------------------------------------------------------
Init == /\ cincoming = [c \in Client |-> <<>>]
        /\ sincoming = <<>>
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
=============================================================================
\* Modification History
\* Last modified Sun Jun 24 10:43:49 CST 2018 by hengxin
\* Created Sun Jun 24 10:25:34 CST 2018 by hengxin