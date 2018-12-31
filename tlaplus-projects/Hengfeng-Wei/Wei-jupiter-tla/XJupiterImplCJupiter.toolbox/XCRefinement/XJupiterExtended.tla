-------------------------- MODULE XJupiterExtended --------------------------
(*
XJupiter extended with serial views. This is used to show that XJupiter implements CJupiter.
*)
EXTENDS XJupiter, JupiterSerial
-----------------------------------------------------------------------------
VARIABLES   \* Simulate the behavior of propagating original operations in CJupiter.
    cincomingCJ, \* cincoming for CJupiter which contains original operations 
                 \* instead of transformed ones in XJupiter
    sincomingCJ  \* (not used)

commCJVars == <<cincomingCJ, sincomingCJ>>
varsEx == <<commCJVars, serialVars, vars>>

commCJ == INSTANCE CSComm WITH Msg <- Seq(Cop), 
                cincoming <- cincomingCJ, sincoming <- sincomingCJ
-----------------------------------------------------------------------------
TypeOKEx == 
    /\ TypeOK
    /\ commCJ!TypeOK
    /\ TypeOKSerial

InitEx == 
    /\ Init
    /\ commCJ!Init
    /\ InitSerial

DoEx(c) == 
    /\ Do(c)
    /\ DoSerial(c)
    /\ UNCHANGED commCJVars

RevEx(c) == 
    /\ Rev(c)
    /\ commCJ!CRev(c)
    /\ RevSerial(c)

SRevEx == 
    /\ SRev
    /\ LET cop == Head(sincoming)
             c == ClientOf(cop)
       IN  /\ commCJ!SSendSame(c, cop)
    /\ SRevSerial
    /\ UNCHANGED sincomingCJ
-----------------------------------------------------------------------------
NextEx == 
    \/ \E c \in Client: DoEx(c) \/ RevEx(c)
    \/ SRevEx

FairnessEx ==
    /\ WF_varsEx(SRevEx \/ \E c \in Client: RevEx(c))

SpecEx == InitEx /\ [][NextEx]_varsEx \* /\ FairnessEx
=============================================================================
\* Modification History
\* Last modified Mon Dec 31 20:52:00 CST 2018 by hengxin
\* Created Tue Oct 30 20:32:27 CST 2018 by hengxin