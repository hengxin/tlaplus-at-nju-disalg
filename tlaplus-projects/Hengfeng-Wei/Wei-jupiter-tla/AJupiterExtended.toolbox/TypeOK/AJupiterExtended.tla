-------------------------- MODULE AJupiterExtended --------------------------
(*
AJupiter extended with JupiterCtx.
This is used to show that AJupiter implements XJupiter.
*)
EXTENDS JupiterCtx
-----------------------------------------------------------------------------
VARIABLES cbuf, crec, sbuf, srec     

vars == <<intVars, ctxVars, cbuf, crec, sbuf, srec>>

Msg == [c: Client, ack: Int, cop: Cop, oid: Oid] \cup [ack: Int, cop: Cop, oid: Oid] 
-----------------------------------------------------------------------------
TypeOK == 
    /\ TypeOKInt
    /\ TypeOKCtx
    /\ Comm(Msg)!TypeOK
    /\ crec \in [Client -> Int]
    /\ srec \in [Client -> Int]
    /\ cbuf \in [Client -> Seq(Cop)]
    /\ sbuf \in [Client -> Seq(Cop)]
-----------------------------------------------------------------------------
Init == 
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

Do(c) == 
    /\ DoCtx(c)
    /\ \/ DoIns(c) 
       \/ DoDel(c)
    /\ UNCHANGED <<sbuf, srec>>
-----------------------------------------------------------------------------
(* 
Client c \in Client receives a message from the Server.           
*)
Rev(c) == 
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
SRev == 
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
Next == 
    \/ \E c \in Client: Do(c) \/ Rev(c)
    \/ SRev

Fairness == \* There is no requirement that the clients ever generate operations.
    WF_vars(SRev \/ \E c \in Client: Rev(c))
    
Spec == Init /\ [][Next]_vars \* /\ Fairness
-----------------------------------------------------------------------------
QC == \* Quiescent Consistency 
    Comm(Msg)!EmptyChannel => Cardinality(Range(state)) = 1

THEOREM Spec => []QC
=============================================================================
\* Modification History
\* Last modified Sat Dec 29 17:42:49 CST 2018 by hengxin
\* Created Thu Dec 27 21:15:09 CST 2018 by hengxin