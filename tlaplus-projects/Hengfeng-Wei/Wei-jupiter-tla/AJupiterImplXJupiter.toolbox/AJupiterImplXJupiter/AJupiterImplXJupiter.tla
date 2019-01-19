------------------------ MODULE AJupiterImplXJupiter ------------------------
EXTENDS AJupiterExtended, GraphStateSpace
-----------------------------------------------------------------------------
VARIABLES c2ss, s2ss

varsImpl == <<varsEx, c2ss, s2ss>>
-----------------------------------------------------------------------------
TypeOKImpl ==
    /\ TypeOKEx
    /\ \A c \in Client: IsSS(c2ss[c]) /\ IsSS(s2ss[c])

InitImpl ==
    /\ InitEx
    /\ c2ss = [c \in Client |-> EmptySS]    
    /\ s2ss = [c \in Client |-> EmptySS]    
-----------------------------------------------------------------------------
DoOpImpl(c, op) == 
    /\ DoOpEx(c, op)
    /\ LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq[c]], ctx |-> ds[c]] 
       IN  c2ss' = [c2ss EXCEPT ![c] = 
                        @ (+) [node |-> {ds'[c]},
                               edge |-> {[from |-> ds[c], to |-> ds'[c], cop |-> cop]}]]
    /\ UNCHANGED s2ss

ClientPerformImpl(c, m) ==
    /\ LET xform == xFormCopCopsShift(m.cop, cbuf[c], m.ack) \* [xcop, xss, lss]
       IN  c2ss' = [c2ss EXCEPT ![c] = @ (+) xform.xss]
    /\ UNCHANGED s2ss

ServerPerformImpl(m) ==
    /\ LET c == ClientOf(m.cop)
           xform == xFormCopCopsShift(m.cop, sbuf[c], m.ack) \* [xcop, xss, lss]
       IN  s2ss' = [cl \in Client |-> IF cl = c THEN s2ss[cl] (+) xform.xss 
                                                ELSE s2ss[cl] (+) xform.lss]
    /\ UNCHANGED c2ss
-----------------------------------------------------------------------------
DoImpl(c) == 
    /\ DoCtx(c)
    /\ DoInt(DoOpImpl, c) \* TODO: refactor to use DoEx(c); cannot use two DoInt
    /\ UNCHANGED <<sbuf, srec>>

RevImpl(c) ==
    /\ RevEx(c)
    /\ RevInt(ClientPerformImpl, c)

SRevImpl ==
    /\ SRevEx
    /\ SRevInt(ServerPerformImpl)
-----------------------------------------------------------------------------
NextImpl ==
    \/ \E c \in Client: DoImpl(c) \/ RevImpl(c)
    \/ SRevImpl
    
FairnessImpl == 
    WF_varsImpl(SRevImpl \/ \E c \in Client: RevImpl(c)) 

SpecImpl == InitImpl /\ [][NextImpl]_varsImpl \* /\ FairnessImpl
-----------------------------------------------------------------------------
XJ == INSTANCE XJupiter WITH Msg <- Cop,
            cincoming <- cincomingXJ, sincoming <- sincomingXJ

THEOREM SpecImpl => XJ!Spec
=============================================================================
\* Modification History
\* Last modified Sat Jan 19 10:54:42 CST 2019 by hengxin
\* Created Sat Dec 29 18:36:51 CST 2018 by hengxin