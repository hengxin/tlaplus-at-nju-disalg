-------------------------- MODULE AJupiterExtended --------------------------
(*
AJupiter extended with JupiterCtx. This is used to show that AJupiter implements XJupiter.
*)
EXTENDS JupiterCtx
-----------------------------------------------------------------------------
VARIABLES cbuf, crec, sbuf, srec, cincomingXJ, sincomingXJ

commXJVars == <<cincomingXJ, sincomingXJ>>
commXJ == INSTANCE CSComm WITH Msg <- Seq(Cop),
                cincoming <- cincomingXJ, sincoming <- sincomingXJ

varsEx == <<intVars, ctxVars, cbuf, crec, sbuf, srec, commXJVars>>

Msg == [ack: Int, cop: Cop, oid: Oid] 
-----------------------------------------------------------------------------
TypeOKEx == 
    /\ TypeOKInt
    /\ TypeOKCtx
    /\ Comm(Msg)!TypeOK
    /\ commXJ!TypeOK
    /\ crec \in [Client -> Int]
    /\ srec \in [Client -> Int]
    /\ cbuf \in [Client -> Seq(Cop)]
    /\ sbuf \in [Client -> Seq(Cop)]
-----------------------------------------------------------------------------
InitEx == 
    /\ InitInt
    /\ InitCtx
    /\ commXJ!Init
    /\ Comm(Msg)!Init
    /\ crec = [c \in Client |-> 0]
    /\ srec = [c \in Client |-> 0]
    /\ cbuf = [c \in Client |-> <<>>]
    /\ sbuf = [c \in Client |-> <<>>]
-----------------------------------------------------------------------------
DoOpEx(c, op) == 
    LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq'[c]], ctx |-> ds[c]]
    IN /\ crec' = [crec EXCEPT ![c] = 0] 
       /\ cbuf' = [cbuf EXCEPT ![c] = Append(@, cop)] 
       /\ state' = [state EXCEPT ![c] = Apply(op, @)] 
       /\ Comm(Msg)!CSend([ack |-> crec[c], cop |-> cop, oid |-> cop.oid])
       /\ commXJ!CSend(cop)

DoEx(c) == 
    /\ DoCtx(c)
    /\ DoInt(DoOpEx, c)
    /\ UNCHANGED <<sbuf, srec>>

RevEx(c) == 
    /\ Comm(Msg)!CRev(c)
    /\ commXJ!CRev(c)
    /\ crec' = [crec EXCEPT ![c] = @ + 1]
    /\ LET m == Head(cincoming[c]) 
           cBuf == cbuf[c]  
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf))  
           xcop == XformOpOps(COT, m.cop, cShiftedBuf) 
           xcBuf == XformOpsOp(COT, cShiftedBuf, m.cop) 
        IN /\ cbuf' = [cbuf EXCEPT ![c] = xcBuf]
           /\ state' = [state EXCEPT ![c] = Apply(xcop.op, @)] 
    /\ RevCtx(c)
    /\ RevInt(c)
    /\ UNCHANGED <<sbuf, srec>>

SRevEx == 
    /\ Comm(Msg)!SRev
    /\ commXJ!SRev
    /\ LET m == Head(sincoming) 
           c == ClientOf(m.cop)
           cBuf == sbuf[c]      
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf)) 
           xcop == XformOpOps(COT, m.cop, cShiftedBuf) 
           xcBuf == XformOpsOp(COT, cShiftedBuf, m.cop) 
        IN /\ srec' = [cl \in Client |-> 
                            IF cl = c THEN srec[cl] + 1 ELSE 0] 
           /\ sbuf' = [cl \in Client |-> 
                            IF cl = c THEN xcBuf ELSE Append(sbuf[cl], xcop)] 
           /\ state' = [state EXCEPT ![Server] = Apply(xcop.op, @)]  
           /\ Comm(Msg)!SSend(c, [cl \in Client |-> [ack |-> srec[cl], cop |-> xcop, oid |-> xcop.oid]])
           /\ commXJ!SSendSame(c, xcop)
    /\ SRevCtx
    /\ SRevInt
    /\ UNCHANGED <<cbuf, crec>>
-----------------------------------------------------------------------------
NextEx == 
    \/ \E c \in Client: DoEx(c) \/ RevEx(c)
    \/ SRevEx

FairnessEx == \* There is no requirement that the clients ever generate operations.
    WF_varsEx(SRevEx \/ \E c \in Client: RevEx(c))
    
SpecEx == InitEx /\ [][NextEx]_varsEx \* /\ FairnessEx
-----------------------------------------------------------------------------
QC == \* Quiescent Consistency 
    Comm(Msg)!EmptyChannel => Cardinality(Range(state)) = 1

THEOREM SpecEx => []QC
=============================================================================
\* Modification History
\* Last modified Mon Dec 31 21:21:44 CST 2018 by hengxin
\* Created Thu Dec 27 21:15:09 CST 2018 by hengxin