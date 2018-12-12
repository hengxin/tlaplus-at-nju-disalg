-------------------------- MODULE JupiterInterface --------------------------
(*
This module declares the parameters and defines the operators that describe
the interface of a family of Jupiter specs.
*)
EXTENDS Integers, SequenceUtils, OT
-----------------------------------------------------------------------------
CONSTANTS
    Client,     \* the set of client replicas
    Server,     \* the (unique) server replica
    Char,       \* the set of characters allowed to be inserted
    InitState   \* the initial state of each replica

ASSUME \* We assume that all inserted elements are unique.
    /\ Range(InitState) \cap Char = {}  \* due to the uniqueness requirement
----------------------------------------------------------------------
VARIABLES 
    state,  \* state[r]: state (the list content) of replica r \in Replica
    cincoming,  \* cincoming[c]: incoming channel at the client c \in Client
    sincoming,  \* incoming channel at the Server    
    chins   \* a set of chars allowed to insert; this is for model checking

intVars == <<state, cincoming, sincoming, chins>>
----------------------------------------------------------------------
Comm(Msg) == INSTANCE CSComm

Replica == Client \cup {Server}

List == Seq(Char \cup Range(InitState))      \* all possible lists
MaxLen == Cardinality(Char) + Len(InitState) \* the max length of lists in any states

ClientNum == Cardinality(Client)
Priority == CHOOSE f \in [Client -> 1 .. ClientNum] : Injective(f)
-----------------------------------------------------------------------------
TypeOKInt ==
    /\ state \in [Replica -> List]
    /\ chins \subseteq Char

InitInt ==
    /\ state = [r \in Replica |-> InitState]
    /\ chins = Char
-----------------------------------------------------------------------------
(*
The set of all operations. Note: The positions are indexed from 1.
*)
Rd == [type: {"Rd"}]
Del == [type: {"Del"}, pos: 1 .. MaxLen]
Ins == [type: {"Ins"}, pos: 1 .. (MaxLen + 1), ch: Char, pr: 1 .. ClientNum] \* pr: priority

Op == Ins \cup Del  \* Now we don't consider Rd operations
=============================================================================
\* Modification History
\* Last modified Thu Dec 06 10:35:54 CST 2018 by hengxin
\* Created Tue Dec 04 19:01:01 CST 2018 by hengxin