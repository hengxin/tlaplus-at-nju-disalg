------------------------------- MODULE CSComm -------------------------------
(* 
Specification of communication in a Client-Server system model.
*)
EXTENDS SequenceUtils
-----------------------------------------------------------------------------
CONSTANTS
    Client,    \* the set of clients
    Server,    \* the (unique) server
    Msg        \* the set of possible messages
-----------------------------------------------------------------------------
VARIABLES
    cincoming,  \* cincoming[c]: incoming channel at client c \in Client
    sincoming   \* incoming channel at the Server
-----------------------------------------------------------------------------
TypeOK == 
    /\ cincoming \in [Client -> Seq(Msg)]
    /\ sincoming \in Seq(Msg)
-----------------------------------------------------------------------------
Init == 
    /\ cincoming = [c \in Client |-> <<>>]
    /\ sincoming = <<>>
-----------------------------------------------------------------------------
(* 
A client sends a message msg to the Server.
*)
CSend(msg) == 
    /\ sincoming' = Append(sincoming, msg)
    /\ UNCHANGED cincoming
(* 
Client c receives a message from the Server.                  
*)
CRev(c) ==
    /\ cincoming[c] # <<>>
    /\ cincoming' = [cincoming EXCEPT ![c] = Tail(@)]   \* consume a message
    /\ UNCHANGED sincoming
-----------------------------------------------------------------------------
(* 
SRev/SSend below is often used as a subaction.      
No UNCHANGED in their definitions.                                             
*)
(*
The Server receives a message.      
*)
SRev == 
    /\ sincoming # <<>>
    /\ sincoming' = Tail(sincoming) \* consume a message
(* 
The Server sents a message cmsg to each client other than c \in Client.
*)
SSend(c, cmsg) ==
    /\ cincoming' = [cl \in Client |->
                        IF cl = c
                        THEN cincoming[cl]
                        ELSE Append(cincoming[cl], cmsg[cl])]
(* 
The Server broadcasts the same message msg to all Clients other than c \in Client.                                         
*)
SSendSame(c, msg) ==
    /\ SSend(c, [cl \in Client |-> msg])
-----------------------------------------------------------------------------
(*
Properties of communication channels.
*)
EmptyChannel == Init
=============================================================================
\* Modification History
\* Last modified Mon Dec 03 20:15:18 CST 2018 by hengxin
\* Created Sun Jun 24 10:25:34 CST 2018 by hengxin