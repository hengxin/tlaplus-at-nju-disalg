---------------------------- MODULE SystemModel ----------------------------
(*
Constants and related definitions describing the system model of Jupiter protocols.
*)
EXTENDS Naturals, SequenceUtils 
----------------------------------------------------------------------
CONSTANTS
    Client,     \* the set of client replicas
    Server,     \* the (unique) server replica
    Msg,        \* the set of messages
    Char,       \* the set of characters
    InitState   \* the initial state of each replica

ASSUME \* We assume that all inserted elements are unique.
    /\ Range(InitState) \cap Char = {}  \* due to the uniqueness requirement
----------------------------------------------------------------------
Replica == Client \cup {Server}

List == Seq(Char \cup Range(InitState)) \* all possible lists
----------------------------------------------------------------------
VARIABLES 
    cincoming,  \* cincoming[c]: incoming channel at the client c \in Client
    sincoming   \* incoming channel at the Server    

Comm == INSTANCE CSComm
=============================================================================
\* Modification History
\* Last modified Mon Jan 14 17:24:11 CST 2019 by hengxin
\* Created Sun Jan 13 09:51:52 CST 2019 by hengxin