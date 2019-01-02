-------------------------- MODULE JupiterInterface --------------------------
(*
This module declares the parameters and defines the operators that describe
the interface of a family of Jupiter specs.
*)
EXTENDS SequenceUtils, OT
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
    aop,    \* op[r]: the actual operation applied at replica r \in Replica
    state,  \* state[r]: state (the list content) of replica r \in Replica
    cincoming,  \* cincoming[c]: incoming channel at the client c \in Client
    sincoming,  \* incoming channel at the Server    
    chins   \* a set of chars allowed to insert; this is for model checking

intVars == <<aop, state, cincoming, sincoming, chins>>
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

SetNewAop(r, aopr) ==
    aop' = [aop EXCEPT ![r] = aopr]

ApplyNewAop(r) ==
    state' = [state EXCEPT ![r] = Apply(aop'[r], @)]
-----------------------------------------------------------------------------
TypeOKInt ==
    /\ aop \in [Replica -> Op \cup {Nop}]
    /\ state \in [Replica -> List]
    /\ chins \subseteq Char

InitInt ==
    /\ aop = [r \in Replica |-> Nop]
    /\ state = [r \in Replica |-> InitState]
    /\ chins = Char
    
DoIns(DoOp(_, _), c) == \* Client c \in Client generates an "Ins" operation.
    \E ins \in Ins: 
        /\ ins.pos \in 1 .. (Len(state[c]) + 1) 
        /\ ins.ch \in chins 
        /\ ins.pr = Priority[c]
        /\ DoOp(c, ins)
        /\ chins' = chins \ {ins.ch} \* We assume that all inserted elements are unique.

DoDel(DoOp(_, _), c) == \* Client c \in Client generates a "Del" operation.
    \E del \in Del: 
        /\ del.pos \in 1 .. Len(state[c])
        /\ DoOp(c, del)
        /\ UNCHANGED chins

DoInt(DoOp(_, _), c) == \* Client c \in Client issues an operation.
    /\ \/ DoIns(DoOp, c) 
       \/ DoDel(DoOp, c)
    /\ ApplyNewAop(c)
    
RevInt(c) == \* Client c \in Client receives a message from the Server.
    /\ ApplyNewAop(c)
    /\UNCHANGED chins

SRevInt == \* The Server receives a message.
    /\ ApplyNewAop(Server)
    /\ UNCHANGED chins
=============================================================================
\* Modification History
\* Last modified Wed Jan 02 14:21:57 CST 2019 by hengxin
\* Created Tue Dec 04 19:01:01 CST 2018 by hengxin