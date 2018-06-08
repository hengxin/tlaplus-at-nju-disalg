
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

