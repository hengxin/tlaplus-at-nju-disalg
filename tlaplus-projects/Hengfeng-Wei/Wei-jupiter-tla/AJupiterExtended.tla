-------------------------- MODULE AJupiterExtended --------------------------
(*
AJupiter extended with JupiterCtx.
This is used to show that AJupiter implements XJupiter.
*)
EXTENDS JupiterCtx
-----------------------------------------------------------------------------
VARIABLES cbuf, crec, sbuf, srec     

varsEx == <<intVars, ctxVars, cbuf, crec, sbuf, srec>>

Msg == [ack: Int, cop: Cop, oid: Oid] 
-----------------------------------------------------------------------------
TypeOKEx == 
    /\ TypeOKInt
    /\ TypeOKCtx
    /\ Comm(Msg)!TypeOK
    /\ crec \in [Client -> Int]
    /\ srec \in [Client -> Int]
    /\ cbuf \in [Client -> Seq(Cop)]
    /\ sbuf \in [Client -> Seq(Cop)]
-----------------------------------------------------------------------------
InitEx == 
    /\ InitInt
    /\ InitCtx
    /\ Comm(Msg)!Init
    /\ crec = [c \in Client |-> 0]
    /\ srec = [c \in Client |-> 0]
    /\ cbuf = [c \in Client |-> <<>>]
    /\ sbuf = [c \in Client |-> <<>>]
-----------------------------------------------------------------------------
(* 
Client c \in Client issues an operation op.                       
*)
DoOp(c, op) == 
    LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq'[c]], ctx |-> ds[c]]
    IN /\ crec' = [crec EXCEPT ![c] = 0] 
       /\ cbuf' = [cbuf EXCEPT ![c] = Append(@, cop)] 
       /\ state' = [state EXCEPT ![c] = Apply(op, @)] 
       /\ Comm(Msg)!CSend([ack |-> crec[c], cop |-> cop, oid |-> cop.oid])

DoIns(c) ==
    \E ins \in {op \in Ins: op.pos \in 1 .. (Len(state[c]) + 1) /\ op.ch \in chins /\ op.pr = Priority[c]}:
        /\ DoOp(c, ins)
        /\ chins' = chins \ {ins.ch} 

DoDel(c) == 
    \E del \in {op \in Del: op.pos \in 1 .. Len(state[c])}:
        /\ DoOp(c, del)
        /\ UNCHANGED chins

DoEx(c) == 
    /\ DoCtx(c)
    /\ \/ DoIns(c) 
       \/ DoDel(c)
    /\ UNCHANGED <<sbuf, srec>>
-----------------------------------------------------------------------------
(* 
Client c \in Client receives a message from the Server.           
*)
RevEx(c) == 
    /\ Comm(Msg)!CRev(c)
    /\ crec' = [crec EXCEPT ![c] = @ + 1]
    /\ LET m == Head(cincoming[c]) 
           cBuf == cbuf[c]  
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf))  
           xcop == XformOpOps(COT, m.cop, cShiftedBuf) 
           xcBuf == XformOpsOp(COT, cShiftedBuf, m.cop) 
        IN /\ cbuf' = [cbuf EXCEPT ![c] = xcBuf]
           /\ state' = [state EXCEPT ![c] = Apply(xcop.op, @)] 
    /\ RevCtx(c)
    /\ UNCHANGED <<chins, sbuf, srec>>
-----------------------------------------------------------------------------
(* 
The Server receives a message.                                    
*)
SRevEx == 
    /\ Comm(Msg)!SRev
    /\ LET m == Head(sincoming) 
           c == ClientOf(m.cop)
           cBuf == sbuf[c]      
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf)) 
           xcop == XformOpOps(COT, m.cop, cShiftedBuf) 
           xcBuf == XformOpsOp(COT, cShiftedBuf, m.cop) 
        IN /\ srec' = [cl \in Client |-> 
                            IF cl = c
                            THEN srec[cl] + 1 
                            ELSE 0] 
           /\ sbuf' = [cl \in Client |->
                            IF cl = c
                            THEN xcBuf  
                            ELSE Append(sbuf[cl], xcop)] 
           /\ state' = [state EXCEPT ![Server] = Apply(xcop.op, @)]  
           /\ Comm(Msg)!SSend(c, [cl \in Client |-> [ack |-> srec[cl], cop |-> xcop, oid |-> xcop.oid]])
    /\ SRevCtx
    /\ UNCHANGED <<chins, cbuf, crec>>
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
\* Last modified Sat Dec 29 18:55:12 CST 2018 by hengxin
\* Created Thu Dec 27 21:15:09 CST 2018 by hengxin