--------------------------- MODULE JupiterSerial ---------------------------
(*
Specification of serial views used by AbsJupiter and CJupiter.
*)
EXTENDS JupiterCtx
-----------------------------------------------------------------------------
VARIABLES
    serial, \* serial[r]: the serial view of replica r \in Replica about the serialization order established at the Server
    cincomingSerial, sincomingSerial

serialVars == <<serial, cincomingSerial, sincomingSerial>>
commSerial == INSTANCE CSComm WITH Msg <- Seq(Oid), 
                cincoming <- cincomingSerial, sincoming <- sincomingSerial
-----------------------------------------------------------------------------
tb(cop1, cop2, sv) == \* Is cop1 totally ordered before cop2 according to the serial view sv (of some replica)?
    LET pos1 == FirstIndexOfElementSafe(sv, cop1) \* 0 if cop1 is not in sv
        pos2 == FirstIndexOfElementSafe(sv, cop2) \* 0 if cop2 is not in sv
    IN  IF pos1 # 0 /\ pos2 # 0 \* at the server or at a client but both are remote operations
        THEN pos1 < pos2        
        ELSE IF pos1 = 0 /\ pos2 = 0 \* at a client: both are local operations (may happen in AbsJupiter)
             THEN cop1.seq < cop2.seq
             ELSE pos1 # 0           \* at a client: one is a remote operation and the other is a local operation
-----------------------------------------------------------------------------
TypeOKSerial ==
    /\ serial \in [Replica -> Seq(Oid)]
    /\ commSerial!TypeOK

InitSerial ==
    /\ serial = [r \in Replica |-> <<>>]
    /\ commSerial!Init

DoSerial(c) ==
    UNCHANGED serialVars

RevSerial(c) ==
    /\ commSerial!CRev(c)
    /\ serial' = [serial EXCEPT ![c] = Head(cincomingSerial[c])]

SRevSerial ==
    /\ LET cop == Head(sincoming)
       IN  /\ serial' = [serial EXCEPT ![Server] = Append(@, cop.oid)]
           /\ commSerial!SSendSame(ClientOf(cop), serial'[Server])
    /\ UNCHANGED sincomingSerial
=============================================================================
\* Modification History
\* Last modified Sat Jan 05 16:27:57 CST 2019 by hengxin
\* Created Wed Dec 05 21:03:01 CST 2018 by hengxin