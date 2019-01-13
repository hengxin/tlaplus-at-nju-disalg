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

List == Seq(Char \cup Range(InitState))      \* all possible lists
MaxLen == Cardinality(Char) + Len(InitState) \* the max length of lists in any state

ClientNum == Cardinality(Client)
Priority == CHOOSE f \in [Client -> 1 .. ClientNum] : Injective(f)
=============================================================================
\* Modification History
\* Last modified Sun Jan 13 09:55:59 CST 2019 by hengxin
\* Created Sun Jan 13 09:51:52 CST 2019 by hengxin