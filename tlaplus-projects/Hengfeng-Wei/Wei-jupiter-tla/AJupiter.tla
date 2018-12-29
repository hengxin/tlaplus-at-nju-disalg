------------------------------ MODULE AJupiter ------------------------------
(* 
Specification of the Jupiter protocol presented by Hagit Attiya and others.
*)
EXTENDS JupiterInterface
-----------------------------------------------------------------------------
VARIABLES
    cbuf,    \* cbuf[c]: buffer for locally generated operations at client c \in Client
    crec,    \* crec[c]: number of remote operations received by client c \in Client
                    \* since the last time a local operation was generated
    sbuf,    \* sbuf[c]: buffer for transformed remote operations w.r.t client c \in Client
    srec     \* srec[c]: number of locally generated operations by client c \in Client
                    \* since the last time a remote operation was transformed at the Server

vars == <<intVars, cbuf, crec, sbuf, srec>>

Msg == [c: Client, ack: Int, op: Op \cup {Nop}] \cup \* messages sent to the Server from a client c \in Client
       [ack: Int, op: Op \cup {Nop}] \* messages broadcast to Clients from the Server
-----------------------------------------------------------------------------
TypeOK == 
    /\ TypeOKInt
    /\ Comm(Msg)!TypeOK
    /\ cbuf \in [Client -> Seq(Op \cup {Nop})]
    /\ crec \in [Client -> Int]
    /\ sbuf \in [Client -> Seq(Op \cup {Nop})]
    /\ srec \in [Client -> Int]
-----------------------------------------------------------------------------
Init == 
    /\ InitInt
    /\ Comm(Msg)!Init
    /\ cbuf = [c \in Client |-> <<>>]
    /\ crec = [c \in Client |-> 0]
    /\ sbuf = [c \in Client |-> <<>>]
    /\ srec = [c \in Client |-> 0]
-----------------------------------------------------------------------------
(* 
Client c \in Client issues an operation op.                       
*)
DoOp(c, op) == 
    /\ state' = [state EXCEPT ![c] = Apply(op, @)] 
    /\ cbuf' = [cbuf EXCEPT ![c] = Append(@, op)]
    /\ crec' = [crec EXCEPT ![c] = 0]
    /\ Comm(Msg)!CSend([c |-> c, ack |-> crec[c], op |-> op])

DoIns(c) ==
    \E ins \in {op \in Ins: op.pos \in 1 .. (Len(state[c]) + 1) /\ op.ch \in chins /\ op.pr = Priority[c]}:
        /\ DoOp(c, ins)
        /\ chins' = chins \ {ins.ch}

DoDel(c) == 
    \E del \in {op \in Del: op.pos \in 1 .. Len(state[c])}:
        /\ DoOp(c, del)
        /\ UNCHANGED chins

Do(c) == 
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
           xop == XformOpOps(Xform, m.op, cShiftedBuf) 
           xcBuf == XformOpsOp(Xform, cShiftedBuf, m.op)
        IN /\ cbuf' = [cbuf EXCEPT ![c] = xcBuf]
           /\ state' = [state EXCEPT ![c] = Apply(xop, @)] 
    /\ UNCHANGED <<chins, sbuf, srec>>
-----------------------------------------------------------------------------
(* 
The Server receives a message.                                    
*)
SRev == 
    /\ Comm(Msg)!SRev
    /\ LET m == Head(sincoming) 
           c == m.c             
           cBuf == sbuf[c]      
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf))
           xop == XformOpOps(Xform, m.op, cShiftedBuf) 
           xcBuf == XformOpsOp(Xform, cShiftedBuf, m.op) 
        IN /\ srec' = [cl \in Client |-> 
                            IF cl = c
                            THEN srec[cl] + 1 
                            ELSE 0] 
           /\ sbuf' = [cl \in Client |->
                            IF cl = c
                            THEN xcBuf  
                            ELSE Append(sbuf[cl], xop)] 
           /\ state' = [state EXCEPT ![Server] = Apply(xop, @)]  
           /\ Comm(Msg)!SSend(c, [cl \in Client |-> [ack |-> srec[cl], op |-> xop]])
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
\* Last modified Sat Dec 29 17:25:40 CST 2018 by hengxin
\* Created Sat Jun 23 17:14:18 CST 2018 by hengxin