--------------------------- MODULE JupiterSerial ---------------------------
(*
This module contains definitions and operators for Jupiter protocols,
i.e., AbsJupiter and CJupiter,
which utilizes the serialization order at the Server to guide OTs.
*)
EXTENDS JupiterCtx
-----------------------------------------------------------------------------
(* 
tb: Is cop1 totally ordered before cop2?
This can be determined according to the serial view (sv) of any replica.
*)
tb(cop1, cop2, sv) == 
    LET pos1 == FirstIndexOfElementSafe(sv, cop1)
        pos2 == FirstIndexOfElementSafe(sv, cop2)
     IN IF pos1 # 0 /\ pos2 # 0 \* at the server or both are remote operations
        THEN pos1 < pos2        
        ELSE IF pos1 = 0 /\ pos2 = 0 \* at a client: both are local operations (not happen in CJupiter)
             THEN cop1.seq < cop2.seq
             ELSE pos1 # 0           \* at a client: one is a remote operation and the other is a local operation
-----------------------------------------------------------------------------
VARIABLES
    serial, \* serial[r]: the serial view of replica r \in Replica about the Server
    cincomingSerial, sincomingSerial

serialVars == <<serial, cincomingSerial, sincomingSerial>>
commSerial == INSTANCE CSComm WITH Msg <- Seq(Oid), 
                cincoming <- cincomingSerial, sincoming <- sincomingSerial
-----------------------------------------------------------------------------
TypeOKSerial ==
    /\ serial \in [Replica -> Seq(Oid)]
    /\ commSerial!TypeOK
-----------------------------------------------------------------------------
InitSerial ==
    /\ serial = [r \in Replica |-> <<>>]
    /\ commSerial!Init

DoSerial(c) ==
    UNCHANGED <<serialVars>>

RevSerial(c) ==
    /\ commSerial!CRev(c)
    /\ serial' = [serial EXCEPT ![c] = Head(cincomingSerial[c])]

SRevSerial ==
    /\ LET cop == Head(sincoming)
       IN  /\ serial' = [serial EXCEPT ![Server] = Append(@, cop.oid)]
           /\ commSerial!SSendSame(cop.oid.c, serial'[Server])
    /\ UNCHANGED <<sincomingSerial>>
=============================================================================
\* Modification History
\* Last modified Wed Dec 12 21:04:36 CST 2018 by hengxin
\* Created Wed Dec 05 21:03:01 CST 2018 by hengxin