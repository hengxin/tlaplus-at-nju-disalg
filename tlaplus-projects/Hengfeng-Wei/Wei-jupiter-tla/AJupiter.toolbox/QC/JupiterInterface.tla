-------------------------- MODULE JupiterInterface --------------------------
(*
Interface of a family of Jupiter protocols.
*)
EXTENDS SequenceUtils, OT
-----------------------------------------------------------------------------
CONSTANTS
    Client,     \* the set of client replicas
    Server,     \* the (unique) server replica
    Msg,        \* the set of messages
    Char,       \* the set of characters
    InitState   \* the initial state of each replica

ASSUME \* We assume that all inserted elements are unique.
    /\ Range(InitState) \cap Char = {}  \* due to the uniqueness requirement
----------------------------------------------------------------------
VARIABLES 
    aop,    \* aop[r]: the actual operation applied at replica r \in Replica
    state,  \* state[r]: state (the list content) of replica r \in Replica
    cincoming,  \* cincoming[c]: incoming channel at the client c \in Client
    sincoming,  \* incoming channel at the Server    
    chins   \* a set of chars allowed to insert; this is for model checking

Comm == INSTANCE CSComm
intVars == <<aop, state, cincoming, sincoming, chins>>
----------------------------------------------------------------------
Replica == Client \cup {Server}

List == Seq(Char \cup Range(InitState))      \* all possible lists
MaxLen == Cardinality(Char) + Len(InitState) \* the max length of lists in any state

ClientNum == Cardinality(Client)
Priority == CHOOSE f \in [Client -> 1 .. ClientNum] : Injective(f)
-----------------------------------------------------------------------------
Rd == [type: {"Rd"}]
Del == [type: {"Del"}, pos: 1 .. MaxLen] \* The positions (pos) are indexed from 1.
Ins == [type: {"Ins"}, pos: 1 .. (MaxLen + 1), ch: Char, pr: 1 .. ClientNum] \* pr: priority

Op == Ins \cup Del  \* The set of all operations (now we don't consider Rd operations).

SetNewAop(r, aopr) ==
    aop' = [aop EXCEPT ![r] = aopr]

ApplyNewAop(r) ==
    state' = [state EXCEPT ![r] = Apply(aop'[r], @)]
-----------------------------------------------------------------------------
TypeOKInt ==
    /\ aop \in [Replica -> Op \cup {Nop}]
    /\ state \in [Replica -> List]
    /\ Comm!TypeOK
    /\ chins \subseteq Char

InitInt ==
    /\ aop = [r \in Replica |-> Nop]
    /\ state = [r \in Replica |-> InitState]
    /\ Comm!Init
    /\ chins = Char
    
DoIns(DoOp(_, _), c) == \* Client c \in Client generates and processes an "Ins" operation.
    \E ins \in Ins: 
        /\ ins.pos \in 1 .. (Len(state[c]) + 1) 
        /\ ins.ch \in chins 
        /\ ins.pr = Priority[c]
        /\ DoOp(c, ins)
        /\ chins' = chins \ {ins.ch} \* We assume that all inserted elements are unique.

DoDel(DoOp(_, _), c) == \* Client c \in Client generates and processes a "Del" operation.
    \E del \in Del: 
        /\ del.pos \in 1 .. Len(state[c])
        /\ DoOp(c, del)
        /\ UNCHANGED chins

DoInt(DoOp(_, _), c) == \* Client c \in Client generates an operation.
    /\ \/ DoIns(DoOp, c)\* DoOp(c \in Client, op \in Op) 
       \/ DoDel(DoOp, c)
    /\ ApplyNewAop(c)
    
RevInt(ClientPerform(_, _), c) == \* Client c \in Client receives and processes a message.
    /\ Comm!CRev(c)
    /\ ClientPerform(c, Head(cincoming[c])) \* ClientPerform(c \in Client, m \in Msg)
    /\ ApplyNewAop(c)
    /\ UNCHANGED chins

SRevInt(ServerPerform(_)) == \* The Server receives and processes a message.
    /\ Comm!SRev
    /\ ServerPerform(Head(sincoming)) \* ServerPerform(m \in Msg)
    /\ ApplyNewAop(Server)
    /\ UNCHANGED chins
=============================================================================
\* Modification History
\* Last modified Fri Jan 04 11:46:40 CST 2019 by hengxin
\* Created Tue Dec 04 19:01:01 CST 2018 by hengxin