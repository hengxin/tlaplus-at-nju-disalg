------------------------------ MODULE CJupiter ------------------------------

(***************************************************************************)
(* Model checking our own CJupiter protocol.                               *)
(***************************************************************************)

CONSTANTS
    Server, \* the server replica
    Client  \* the set of client replicas
    
VARIABLES
    cin, \* cin[c]: incoming channel of c \in Client
    sin  \* sin[c]: incoming channel for c \in Client at the Server
=============================================================================
\* Modification History
\* Last modified Sat Jun 09 00:46:54 CST 2018 by hengxin
\* Created Sat Jun 09 00:42:52 CST 2018 by hengxin
