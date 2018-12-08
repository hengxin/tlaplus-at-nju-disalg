-------------------------- MODULE JupiterInterface --------------------------
(*
This module declares the parameters and defines the operators that describe
the interface of a family of Jupiter specs.
*)
EXTENDS Integers, SequenceUtils
-----------------------------------------------------------------------------
CONSTANTS
    Client,     \* the set of client replicas
    Server,     \* the (unique) server replica
    Char,       \* set of characters allowed
    InitState   \* the initial state of each replica

Replica == Client \cup {Server}

List == Seq(Char \cup Range(InitState))      \* all possible lists/strings
MaxLen == Cardinality(Char) + Len(InitState) \* the max length of lists in any states;
    \* We assume that all inserted elements are unique.

ClientNum == Cardinality(Client)
Priority == CHOOSE f \in [Client -> 1 .. ClientNum] : Injective(f)
----------------------------------------------------------------------
ASSUME 
    /\ Range(InitState) \cap Char = {}  \* due to the uniqueness requirement
    /\ Priority \in [Client -> 1 .. ClientNum]
-----------------------------------------------------------------------------
(*
The set of all operations. Note: The positions are indexed from 1.
*)
(*********************************************************************)
Rd == [type: {"Rd"}]
Del == [type: {"Del"}, pos: 1 .. MaxLen]
Ins == [type: {"Ins"}, pos: 1 .. (MaxLen + 1), ch: Char, pr: 1 .. ClientNum] \* pr: priority

Op == Ins \cup Del  \* Now we don't consider Rd operations
=============================================================================
\* Modification History
\* Last modified Tue Dec 04 19:16:22 CST 2018 by hengxin
\* Created Tue Dec 04 19:01:01 CST 2018 by hengxin