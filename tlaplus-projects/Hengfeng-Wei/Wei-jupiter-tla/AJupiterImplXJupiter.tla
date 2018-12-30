------------------------ MODULE AJupiterImplXJupiter ------------------------
(*
We show that AJupiter (specifically, AJupiterExtended) implements XJupiter.
*)
EXTENDS AJupiterExtended, StateSpace
-----------------------------------------------------------------------------
VARIABLES c2ss, s2ss

varsImpl == <<varsEx, c2ss, s2ss>>
-----------------------------------------------------------------------------
TypeOKImpl ==
    /\ TypeOKEx
    /\ \A c \in Client: IsSS(c2ss[c]) /\ IsSS(s2ss[c])
-----------------------------------------------------------------------------
InitImpl ==
    /\ InitEx
    /\ c2ss = [c \in Client |-> EmptySS]    
    /\ s2ss = [c \in Client |-> EmptySS]    
-----------------------------------------------------------------------------
DoImpl(c) == TRUE
-----------------------------------------------------------------------------
RevImpl(c) ==
    /\ RevEx(c)
    /\ LET m == Head(cincoming[c])
           cBuf == cbuf[c]
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf))  
        IN TRUE
=============================================================================
\* Modification History
\* Last modified Sat Dec 29 19:26:35 CST 2018 by hengxin
\* Created Sat Dec 29 18:36:51 CST 2018 by hengxin