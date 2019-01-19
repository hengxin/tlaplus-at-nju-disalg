------------------------ MODULE XJupiterImplCJupiter ------------------------
EXTENDS XJupiterExtended
-----------------------------------------------------------------------------
VARIABLES
    op2ss,  \* a function mapping an operation (identifier) 
            \* to the 2D state space created during it is transformed
    c2ssX   \* c2ssX[c]: redundant (eXtra) 2D state space maintained for client c \in Client

varsImpl == <<varsEx, op2ss, c2ssX>>
-----------------------------------------------------------------------------
TypeOKImpl ==
    /\ TypeOKEx
    /\ \A oid \in DOMAIN op2ss: oid \in Oid /\ IsSS(op2ss[oid])
    /\ \A c \in Client: IsSS(c2ssX[c])

InitImpl ==
    /\ InitEx
    /\ op2ss = <<>>
    /\ c2ssX = [c \in Client |-> EmptySS]

DoImpl(c) ==
    /\ DoEx(c)
    /\ UNCHANGED <<op2ss, c2ssX>>

RevImpl(c) ==
    /\ RevEx(c)
    /\ LET cop == Head(cincoming[c])
       IN  c2ssX' = [c2ssX EXCEPT ![c] = @ (+) op2ss[cop.oid]]
    /\ UNCHANGED op2ss

SRevImpl == 
    /\ SRevEx
    /\ LET cop == Head(sincoming)
             c == ClientOf(cop)
         xform == xForm(NextEdge, Server, cop, s2ss[c])  \* TODO: performance!!!
       IN op2ss' = op2ss @@ cop.oid :> xform.xss
    /\ UNCHANGED c2ssX
-----------------------------------------------------------------------------
NextImpl ==
    \/ \E c \in Client: DoImpl(c) \/ RevImpl(c)
    \/ SRevImpl
    
FairnessImpl ==
    WF_varsImpl(SRevImpl \/ \E c \in Client: RevImpl(c)) 

SpecImpl == InitImpl /\ [][NextImpl]_varsImpl \* /\ FairnessImpl
-----------------------------------------------------------------------------
CJ == INSTANCE CJupiter 
        WITH cincoming <- cincomingCJ, \* sincoming needs no substitution
             css <- [r \in Replica |-> IF r = Server 
                                       THEN SetReduce((+), Range(s2ss), EmptySS)
                                       ELSE c2ss[r] (+) c2ssX[r]]

THEOREM SpecImpl => CJ!Spec
=============================================================================
\* Modification History
\* Last modified Fri Jan 18 11:27:25 CST 2019 by hengxin
\* Created Fri Oct 26 15:00:19 CST 2018 by hengxin