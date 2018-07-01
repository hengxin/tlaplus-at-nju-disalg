
OP == [type : {"Ins", "Del"}, pos : Nat, ch : Char]   \* set of all possible operations; ignoring READ now
MSG == [op: OP, my: Nat, other: Nat]    \* set of all possible messages

TypeOK ==
    
-----------------------------------------------------------------------------
Init ==
    /\ FALSE
-----------------------------------------------------------------------------
Apply(o) == \* TODO: pos? (starting from 1 ???)
    /\ \/ /\ o.type = "Ins"
          /\ str' = Append(SubSeq(str, 1, o.pos-1), o.ch) \o SubSeq(str, o.pos, Len(str))  
       \/ /\ o.type = "Del"
          /\ str' = SubSeq(str, 1, o.pos-1) \o SubSeq(str, o.pos, Len(str))
    /\ UNCHANGED <<myMsgs, otherMsgs, outgoing, incoming>>

Xform(o) ==
    /\ FALSE
    
Issue(node, o) == \* A node issues an operation
    /\ Apply(o)
    /\ incoming' = [incoming EXCEPT ![1 - node] = Append(@,[op |-> o, my |-> myMsgs, other |-> otherMsgs])]
    /\ outgoing' = [outgoing EXCEPT ![node] = Append(@,[op |-> o, my |-> myMsgs, other |-> otherMsgs])]
    /\ myMsgs' = myMsgs + 1
    /\ UNCHANGED otherMsgs

Receive(node, msg) == \* A node receives an message
    /\ incoming[node] # <<>>
    /\ msg = Head(incoming[node])
    /\ incoming' = [incoming EXCEPT ![node] = Tail(@)]  \* removing this msg from incoming; won't receive it again
    /\ outgoing' = [outgoing EXCEPT ![node] = SelectSeq(@, LAMBDA m : m.my < msg.other)]
    /\ Xform(msg.op)
    /\ otherMsgs' = otherMsgs + 1
    /\ UNCHANGED myMsgs
    
Next ==
    \E n \in NODE, o \in OP, m \in MSG: 
    \/ Issue(n, o)
    \/ Receive(n, m) 



(*********************************************************************)
(* Client c \in Client receives a message from the Server.           *)
(*********************************************************************)
CRev(c) == 
    /\ comm!CRev(c)
    /\ crec' = [crec EXCEPT ![c] = @ + 1]
    /\ LET m == Head(cincoming[c]) 
           cBuf == cbuf[c]  \* the buffer at client c \in Client
           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf))  \* buffer shifted
           xop == XformOpOps(m.op, cShiftedBuf) \* transform op vs. shifted buffer
           xcBuf == XformOpsOp(cShiftedBuf, m.op) \* transform shifted buffer vs. op
        IN /\ cbuf' = [cbuf EXCEPT ![c] = xcBuf]
           /\ cstate' = [cstate EXCEPT ![c] = Apply(xop, @)] \* apply the transformed operation xop
    /\ UNCHANGED (sVars \o <<cop>>)

(*********************************************************************)
(* The Server receives a message.                                    *)
(*********************************************************************)
\*SRev == 
\*    /\ comm!SRev
\*    /\ LET m == Head(sincoming) \* the message to handle with
\*           c == m.c             \* the client c \in Client that sends this message
\*           cBuf == sbuf[c]      \* the buffer at the Server for client c \in Client
\*           cShiftedBuf == SubSeq(cBuf, m.ack + 1, Len(cBuf)) \* buffer shifted
\*           xop == XformOpOps(m.op, cShiftedBuf) \* transform op vs. shifted buffer
\*           xcBuf == XformOpsOp(cShiftedBuf, m.op) \* transform shifted buffer vs. op
\*        IN /\ srec' = [cl \in Client |-> 
\*                            IF cl = c
\*                            THEN srec[cl] + 1 \* receive one more operation from client c \in Client
\*                            ELSE 0] \* reset srec for other clients than c \in Client
\*           /\ sbuf' = [cl \in Client |->
\*                            IF cl = c
\*                            THEN xcBuf  \* transformed buffer for client c \in Client
\*                            ELSE Append(sbuf[cl], xop)] \* store transformed xop into other clients' bufs
\*           /\ sstate' = Apply(xop, sstate)  \* apply the transformed operation
\*           /\ comm!SSend(c, srec, xop)
\*    /\ UNCHANGED cVars
-----------------------------------------------------------------------------

\*    \/ \E c \in Client: CRev(c)
\*    \/ SRev
