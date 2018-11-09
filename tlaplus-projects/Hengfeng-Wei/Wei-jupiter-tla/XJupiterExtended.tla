-------------------------- MODULE XJupiterExtended --------------------------
(*
XJupiter extended with serial views. 
This is used to show that XJupiter implements CJupiter.
*)
EXTENDS XJupiter
-----------------------------------------------------------------------------
VARIABLES
    (*
      Simulating the behavior of propagating original operations in CJupiter.
    *)
    cincomingCJ, \* cincoming for CJupiter which contains original operations 
                 \* instead of transformed ones in XJupiter
    sincomingCJ, \* (not used)
    (*
      For edge ordering in CSS. 
    *)
    serial, \* serial[r]: the serial view of replica r \in Replica about the server
    cincomingSerial, \* cincomingSerial[c]: the serival view received by client c \in Client 
                     \* from the Server
    sincomingSerial  \* (not used)

commCJVars == <<cincomingCJ, sincomingCJ>>
serialVars == <<serial, cincomingSerial, sincomingSerial>>
varsEx == <<commCJVars, serialVars, vars>>
-----------------------------------------------------------------------------
commCJ == INSTANCE CSComm WITH Msg <- Seq(Cop), 
                cincoming <- cincomingCJ, sincoming <- sincomingCJ
commSerial == INSTANCE CSComm WITH Msg <- Seq(Oid), 
                cincoming <- cincomingSerial, sincoming <- sincomingSerial
-----------------------------------------------------------------------------
TypeOKEx == 
    /\ TypeOK
    /\ commCJ!TypeOK
    /\ serial \in [Replica -> Seq(Oid)]
    /\ commSerial!TypeOK
-----------------------------------------------------------------------------
InitEx == 
    /\ Init
    /\ commCJ!Init
    /\ serial = [r \in Replica |-> <<>>]
    /\ commSerial!Init
-----------------------------------------------------------------------------
DoEx(c) == 
    /\ Do(c)
    /\ UNCHANGED <<commCJVars, serialVars>>

RevEx(c) == 
    /\ Rev(c)
    /\ commCJ!CRev(c)
    /\ commSerial!CRev(c)
    /\ serial' = [serial EXCEPT ![c] = Head(cincomingSerial[c])]

SRevEx == 
    /\ SRev
    /\ LET cop == Head(sincoming)
             c == cop.oid.c
       IN  /\ commCJ!SSendSame(c, cop)
           /\ serial' = [serial EXCEPT ![Server] = Append(@, cop.oid)] 
           /\ commSerial!SSendSame(c, serial'[Server])
    /\ UNCHANGED <<sincomingCJ, sincomingSerial>>
-----------------------------------------------------------------------------
NextEx == 
    \/ \E c \in Client: DoEx(c) \/ RevEx(c)
    \/ SRevEx

SpecEx == InitEx /\ [][NextEx]_varsEx 
    /\ WF_varsEx(SRevEx \/ \E c \in Client: RevEx(c))
=============================================================================
\* Modification History
\* Last modified Fri Nov 09 17:16:28 CST 2018 by hengxin
\* Created Tue Oct 30 20:32:27 CST 2018 by hengxin