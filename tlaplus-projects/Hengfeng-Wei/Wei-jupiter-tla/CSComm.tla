------------------------------- MODULE CSComm -------------------------------
(* 
Specification of communication in a Client-Server system model.
*)
EXTENDS SequenceUtils
-----------------------------------------------------------------------------
CONSTANTS
    Client, \* the set of clients
    Server, \* the (unique) server
    Msg     \* the set of messages
-----------------------------------------------------------------------------
VARIABLES
    cincoming,  \* cincoming[c]: incoming channel at client c \in Client
    sincoming   \* incoming channel at the Server
-----------------------------------------------------------------------------
TypeOK == 
    /\ cincoming \in [Client -> Seq(Msg)]
    /\ sincoming \in Seq(Msg)

Init == 
    /\ cincoming = [c \in Client |-> <<>>]
    /\ sincoming = <<>>

EmptyChannel == Init
-----------------------------------------------------------------------------
CSend(msg) == \* A client sends a message msg to the Server.
    /\ sincoming' = Append(sincoming, msg)
    /\ UNCHANGED cincoming

CRev(c) == \* Client c receives and consumes a message from the Server.                  
    /\ cincoming[c] # <<>>
    /\ cincoming' = [cincoming EXCEPT ![c] = Tail(@)]
    /\ UNCHANGED sincoming
-----------------------------------------------------------------------------
SRev == \* The Server receives and consumes a message.      
    /\ sincoming # <<>>
    /\ sincoming' = Tail(sincoming)

SSend(c, cmsg) == \* The Server sents a message cmsg to each client other than c \in Client.
    /\ cincoming' = [cl \in Client |-> IF cl = c 
                                       THEN cincoming[cl] 
                                       ELSE Append(cincoming[cl], cmsg[cl])]

SSendSame(c, msg) == \* The Server broadcasts the message msg to all clients other than c \in Client.
    /\ SSend(c, [cl \in Client |-> msg])
=============================================================================
\* Modification History
\* Last modified Thu Jan 03 09:46:24 CST 2019 by hengxin
\* Created Sun Jun 24 10:25:34 CST 2018 by hengxin