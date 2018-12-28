-------------------------- MODULE AJupiterExtended --------------------------
(*
AJupiter extended with JupiterCtx.
This is used to show that AJupiter implements XJupiter.
*)
EXTENDS JupiterInterface
-----------------------------------------------------------------------------
(* 
Messages between the Server and the Clients.
*)
Msg == [c: Client, ack: Int, op: Op \cup {Nop}] \cup \* messages sent to the Server from a client c \in Client
       [ack: Int, op: Op \cup {Nop}] \* messages broadcast to Clients from the Server
-----------------------------------------------------------------------------
VARIABLES
    cbuf,    \* cbuf[c]: buffer (of operations) at the client c \in Client
    crec,    \* crec[c]: the number of new messages have been received by the client c \in Client
                    \* since the last time a message was sent
    sbuf,    \* sbuf[c]: buffer (of operations) at the Server, one per client c \in Client
    srec     \* srec[c]: the number of new messages have been ..., one per client c \in Client

vars == <<intVars, cbuf, crec, sbuf, srec>>
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
        /\ chins' = chins \ {ins.ch} \* We assume that all inserted elements are unique.
        /\ UNCHANGED <<sbuf, srec>>

DoDel(c) == 
    \E del \in {op \in Del: op.pos \in 1 .. Len(state[c])}:
        /\ DoOp(c, del)
        /\ UNCHANGED <<chins, sbuf, srec>>

Do(c) == 
    \/ DoIns(c)
    \/ DoDel(c)
(* 
Client c \in Client receives a message from the Server.           
*)
Rev(c) == 
    /\ Comm(Msg)!CRev(c)
    /\ crec' = [crec EXCEPT ![c] = @ + 1]
    /\ LET m == Head(cincoming[c]) 
           cBuf == cbuf[c]  \* the buffer at client c \in Client
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf))  \* buffer shifted
           xop == XformOpOps(m.op, cShiftedBuf) \* transform op vs. shifted buffer
           xcBuf == XformOpsOp(cShiftedBuf, m.op) \* transform shifted buffer vs. op
        IN /\ cbuf' = [cbuf EXCEPT ![c] = xcBuf]
           /\ state' = [state EXCEPT ![c] = Apply(xop, @)] \* apply the transformed operation xop
    /\ UNCHANGED <<chins, sbuf, srec>>
(* 
The Server receives a message.                                    
*)
SRev == 
    /\ Comm(Msg)!SRev
    /\ LET m == Head(sincoming) \* the message to handle with
           c == m.c             \* the client c \in Client that sends this message
           cBuf == sbuf[c]      \* the buffer at the Server for client c \in Client
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf)) \* buffer shifted
           xop == XformOpOps(m.op, cShiftedBuf) \* transform op vs. shifted buffer
           xcBuf == XformOpsOp(cShiftedBuf, m.op) \* transform shifted buffer vs. op
        IN /\ srec' = [cl \in Client |-> 
                            IF cl = c
                            THEN srec[cl] + 1 \* receive one more operation from client c \in Client
                            ELSE 0] \* reset srec for other clients than c \in Client
           /\ sbuf' = [cl \in Client |->
                            IF cl = c
                            THEN xcBuf  \* transformed buffer for client c \in Client
                            ELSE Append(sbuf[cl], xop)] \* store transformed xop into other clients' bufs
           /\ state' = [state EXCEPT ![Server] = Apply(xop, @)]  \* apply the transformed operation
           /\ Comm(Msg)!SSend(c, [cl \in Client |-> [ack |-> srec[cl], op |-> xop]])
    /\ UNCHANGED <<chins, cbuf, crec>>
-----------------------------------------------------------------------------
Next == 
    \/ \E c \in Client: Do(c) \/ Rev(c)
    \/ SRev
(*
Fairness: There is no requirement that the clients ever generate operations.
*)
Fairness == 
    WF_vars(SRev \/ \E c \in Client: Rev(c))
    
Spec == Init /\ [][Next]_vars \* /\ Fairness
=============================================================================
\* Modification History
\* Last modified Fri Dec 28 10:35:28 CST 2018 by hengxin
\* Created Thu Dec 27 21:15:09 CST 2018 by hengxin