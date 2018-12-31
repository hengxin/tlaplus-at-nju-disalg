-------------------------- MODULE JupiterInterface --------------------------
(*
This module declares the parameters and defines the operators that describe
the interface of a family of Jupiter specs.
*)
EXTENDS Integers, SequenceUtils, OT
-----------------------------------------------------------------------------
CONSTANTS
    Char,       \* the set of characters
    Client,     \* the set of client replicas
    Server,     \* the (unique) server replica
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
MaxLen == Cardinality(Char) + Len(InitState) \* the max length of lists in any state

ClientNum == Cardinality(Client)
Priority == CHOOSE f \in [Client -> 1 .. ClientNum] : Injective(f)
-----------------------------------------------------------------------------
(*
The set of all operations. Note: The positions are indexed from 1.
*)
Rd == [type: {"Rd"}]
Del == [type: {"Del"}, pos: 1 .. MaxLen]
Ins == [type: {"Ins"}, pos: 1 .. (MaxLen + 1), ch: Char, pr: 1 .. ClientNum] \* pr: priority

Op == Ins \cup Del  \* Now we don't consider Rd operations
-----------------------------------------------------------------------------
TypeOKInt ==
    /\ state \in [Replica -> List]
    /\ chins \subseteq Char

InitInt ==
    /\ state = [r \in Replica |-> InitState]
    /\ chins = Char
    
DoIns(DoOp(_, _), c) == \* Client c \in Client generates an "Ins" operation.
    \E ins \in {op \in Ins: 
                    /\ op.pos \in 1 .. (Len(state[c]) + 1) 
                    /\ op.ch \in chins /\ op.pr = Priority[c]}:
        /\ DoOp(c, ins)
        /\ chins' = chins \ {ins.ch} \* We assume that all inserted elements are unique.

DoDel(DoOp(_, _), c) == \* Client c \in Client generates a "Del" operation.
    \E del \in {op \in Del: op.pos \in 1 .. Len(state[c])}:
        /\ DoOp(c, del)
        /\ UNCHANGED chins

DoInt(DoOp(_, _), c) == \* Client c \in Client issues an operation.
    \/ DoIns(DoOp, c)
    \/ DoDel(DoOp, c)
    
RevInt(c) == \* Client c \in Client receives a message from the Server.
    /\UNCHANGED chins

SRevInt == \* The Server receives a message.
    /\ UNCHANGED chins
=============================================================================
\* Modification History
\* Last modified Mon Dec 31 20:27:25 CST 2018 by hengxin
\* Created Tue Dec 04 19:01:01 CST 2018 by hengxin