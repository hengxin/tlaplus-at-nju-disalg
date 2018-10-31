----------------------------- MODULE XCJupiter -----------------------------
(*
Combination of XJupiter and CJupiter.
*)

EXTENDS Integers, OT, TLC, AdditionalFunctionOperators, AdditionalSequenceOperators
-----------------------------------------------------------------------------
CONSTANTS
    Client,     \* the set of client replicas
    Server,     \* the (unique) server replica
    Char,       \* set of characters allowed
    InitState   \* the initial state of each replica

(*
Variables for CJupiter
*)
VARIABLES
    (*****************************************************************)
    (* For the client replicas:                                      *)
    (*****************************************************************)
    cseq,    \* cseq[c]: local sequence number at client c \in Client
    (*****************************************************************)
    (* For the server replica:                                       *)
    (*****************************************************************)
    soids,  \* the set of operations the Server has executed
    (*****************************************************************)
    (* For all replicas: the n-ary ordered state space               *)
    (*****************************************************************)
    css,    \* css[r]: the n-ary ordered state space at replica r \in Replica
    cur,    \* cur[r]: the current node of css at replica r \in Replica
    state,  \* state[r]: state (the list content) of replica r \in Replica
    (*****************************************************************)
    (* For communication between the Server and the Clients:         *)
    (*****************************************************************)
    cincoming,  \* cincoming[c]: incoming channel at the client c \in Client
    sincoming,  \* incoming channel at the Server
    (*****************************************************************)
    (* For model checking:                                           *)
    (*****************************************************************)
    chins   \* a set of chars to insert

cjupiter == INSTANCE CJupiter
=============================================================================
\* Modification History
\* Last modified Wed Oct 24 14:43:27 CST 2018 by hengxin
\* Created Wed Oct 24 14:35:01 CST 2018 by hengxin
