
        


(**********************************************************************)
(* Replica r issues a Send() event, sending an update message.        *)
(**********************************************************************)
Send(r) == /\ acc[r] # 0    \* there are accumulated increments
           /\ acc' = [acc EXCEPT ![r] = 0]  \* reset acc[r]
           /\ Broadcast(r, acc[r])  \* broadcast acc[r] to other replicas
           /\ UNCHANGED <<counter>> 
           
(**********************************************************************)
(* Replica r issues a Receive() event, receiving an update message.   *)
(**********************************************************************)
Receive(r) == /\ incoming[r] # <<>>
              /\ LET m = Head(incoming[r])
                 IN counter' = [counter EXCEPT ![r] = @ + m]
              /\ incoming' = [incoming EXCEPT ![r] = Tail(@)]   \* each message is delivered exactly once
              /\ UNCHANGED <<acc>>
              
(**********************************************************************)
(* The Next-state relation                                            *)
(**********************************************************************)
Next == \E r \in Replica: Inc(r) \/ Send(r) \/ Receive(r)
              
vars = <<counter, acc, incoming>>
Spec == Init /\ [][Next]_vars