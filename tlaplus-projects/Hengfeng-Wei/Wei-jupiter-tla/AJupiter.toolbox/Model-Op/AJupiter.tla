------------------------------ MODULE AJupiter ------------------------------

(***************************************************************************)
(* Model checking the Jupiter protocol presented by Attiya and others.     *)
(***************************************************************************)

EXTENDS Naturals, Sequences
-----------------------------------------------------------------------------
CONSTANTS
    Char,       \* characters allowed in the list
    Server,     \* the (unique) server replica
    Client      \* the set of client replicas
    
VARIABLES
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    cbuf,    \* cbuf[c]: buffer (of operations) at the client c \in Client
    crec,    \* crec[c]: the number of new messages have been received by the client c \in Client
                    \* since the last time a message was sent
    cstate,  \* cstate[c]: state (the list content) of the client c \in Client

    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    sbuf,    \* sbuf[c]: buffer (of operations) at the Server, one per client c \in Client
    srec,    \* srec[c]: the number of new messages have been ..., one per client c \in Client
    sstate   \* sstate: state (the list content) of the server Server
-----------------------------------------------------------------------------
(*********************************************************************)
(* The set of all operations.                                        *)
(* In this specification, we will focus on "Ins" and "Del".          *)
(*********************************************************************)
Op == [type: {"Rd"}] \cup \* a read specifies no arguments
      [type: {"Del"}, pos: Nat \ {0}] \cup \* a deletion specifies a position (from 1)
      [type: {"Ins", "Set"}, pos: Nat \ {0}, ch: Char] \* an insertion or a set specifies a position (from 1) and a character
Nop == CHOOSE v : v \notin Op  \* Nop: an operation representing "doing nothing"
List == Seq(Char)   \* The set of all lists.
-----------------------------------------------------------------------------
TypeOK == 
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    /\ cbuf \in [Client -> Seq(Op)]
    /\ crec \in [Client -> Nat]
    /\ cstate \in [Client -> List]
    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    /\ sbuf \in [Client -> Seq(Op)]
    /\ srec \in [Client -> Nat]
    /\ sstate \in [Client -> List]
-----------------------------------------------------------------------------
(*********************************************************************)
(* The Init predicate.                                               *)
(*********************************************************************)
Init == 
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    /\ cbuf = [c \in Client |-> <<>>]
    /\ crec = [c \in Client |-> 0]
    /\ cstate = [c \in Client |-> <<>>]
    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    /\ sbuf = [c \in Client |-> <<>>]
    /\ srec = [c \in Client |-> 0]
    /\ sstate = [c \in Client |-> <<>>]
-----------------------------------------------------------------------------
(*********************************************************************)
(* The "Apply" operator which applies an operation op on the list l.*)
(*********************************************************************)
Apply(op, l) == 
    /\ op \in Op
    /\ l \in List
    /\ l' = LET len == Len(l)
                pos == op.pos
            IN CASE op.type = "Del" -> SubSeq(l, 1, pos - 1) \o SubSeq(l, pos + 1, len) 
                []  op.type = "Ins" -> Append(SubSeq(l, 1, pos - 1), op.ch) \o SubSeq(l, pos + 1, len)
-----------------------------------------------------------------------------
(*********************************************************************)
(* Client c \in Client generates and performs an operation op.       *)
(*********************************************************************)
Do(c, op) == FALSE
-----------------------------------------------------------------------------
(*********************************************************************)
(* The next state relation                                           *)
(*********************************************************************)
Next == FALSE
=============================================================================
\* Modification History
\* Last modified Sat Jun 23 20:53:22 CST 2018 by hengxin
\* Created Sat Jun 23 17:14:18 CST 2018 by hengxin
