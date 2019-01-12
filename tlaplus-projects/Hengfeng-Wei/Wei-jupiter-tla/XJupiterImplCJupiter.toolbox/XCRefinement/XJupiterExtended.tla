-------------------------- MODULE XJupiterExtended --------------------------
(*
XJupiter extended with serial views. This is used to show that XJupiter implements CJupiter.
*)
EXTENDS XJupiter, JupiterSerial
-----------------------------------------------------------------------------
VARIABLES \* Simulate the behavior of propagating original operations in CJupiter.
    cincomingCJ, \* cincoming for CJupiter which contains original operations 
    sincomingCJ  \* (not used)

commCJVars == <<cincomingCJ, sincomingCJ>>
varsEx == <<commCJVars, serialVars, vars>>

commCJ == INSTANCE CSComm WITH Msg <- Seq(Cop), 
                cincoming <- cincomingCJ, sincoming <- sincomingCJ
-----------------------------------------------------------------------------
TypeOKEx == 
    /\ TypeOK
    /\ TypeOKSerial
    /\ commCJ!TypeOK

InitEx == 
    /\ Init
    /\ InitSerial
    /\ commCJ!Init

DoEx(c) == 
    /\ Do(c)
    /\ DoSerial(c)
    /\ UNCHANGED commCJVars

RevEx(c) == 
    /\ Rev(c)
    /\ RevSerial(c)
    /\ commCJ!CRev(c)

SRevEx == 
    /\ SRev
    /\ SRevSerial
    /\ LET cop == Head(sincoming)
       IN  commCJ!SSendSame(ClientOf(cop), cop)
    /\ UNCHANGED sincomingCJ
-----------------------------------------------------------------------------
NextEx == 
    \/ \E c \in Client: DoEx(c) \/ RevEx(c)
    \/ SRevEx

FairnessEx ==
    WF_varsEx(SRevEx \/ \E c \in Client: RevEx(c))

SpecEx == InitEx /\ [][NextEx]_varsEx \* /\ FairnessEx
=============================================================================
\* Modification History
\* Last modified Sat Jan 12 15:56:59 CST 2019 by hengxin
\* Created Tue Oct 30 20:32:27 CST 2018 by hengxin