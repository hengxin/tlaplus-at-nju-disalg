---------------------------- MODULE StateCounter ----------------------------

(**********************************************************************)
(* TLA+ module for State-based Counter.                               *)
(* See its implementation in paper Burckhardt@POPL'2014.              *)
(* We check that the State-based Counter satisfies the                *)
(* strong eventual convergence property (SEC)                         *)
(**********************************************************************)

EXTENDS Naturals, Sequences, Bags, TLC

CONSTANTS 
    (**********************************************************************)
    (* Protocol variables.                                                *)
    (**********************************************************************)
    Replica,        \* the set of replicas
    (**********************************************************************)
    (* Auxiliary variables for model checking.                            *)
    (**********************************************************************)
    Max             \* Max[r]: the maximum number of the Inc() event replica r \in Replica can issue; 
                    \* for finite-state model checking
    
VARIABLES 
    (**********************************************************************)
    (* Protocol variables.                                                *)
    (**********************************************************************)
    vc,             \* vc[r][r]: the current value of the counter vector at replica r \in Replica
    incoming,       \* incoming[r]: incoming messages at replica r \in Replica
    (**********************************************************************)
    (* Auxiliary variables for model checking.                            *)
    (**********************************************************************)
    inc,            \* inc[r]: the number of Inc() events issued by the replica r \in Replica
    sendAllowed     \* sendAllowed[r]: is the replica r \in Replica allowed to send a message

(**********************************************************************)
(* The type correctness predicate.                                    *)
(**********************************************************************)
TypeOK == /\ vc \in [Replica -> [Replica -> Nat]]
          /\ inc \in [Replica -> Nat]
          /\ sendAllowed \in [Replica -> {0,1}]
          \* /\ incoming \in [Replica -> SubBag(SetToBag(Nat))] \* message ordering is not important; using bag (i.e., multiset)

-----------------------------------------------------------------------------
(**********************************************************************)
(* The initial state predicate.                                       *)
(**********************************************************************)

Init == /\ vc = [r \in Replica |-> [s \in Replica |-> 0]]
        /\ incoming = [r \in Replica |-> EmptyBag]
        /\ inc = [r \in Replica |-> 0]
        /\ sendAllowed = [r \in Replica |-> 0]

-----------------------------------------------------------------------------
(**********************************************************************)
(* Replica r \in Replica issues an Read() event.                      *)
(**********************************************************************)

(**********************************************************************)
(* Replica r \in Replica issues an Inc() event.                       *)
(**********************************************************************)
Inc(r) == /\ inc[r] < Max[r]                   
          \* each replica r \in Replica can issue at most Max[r] Inc() events.
          /\ vc' = [vc EXCEPT ![r][r] = @ + 1] \* current counter + 1
          /\ inc' = [inc EXCEPT ![r] = @ + 1]
          /\ sendAllowed' = [sendAllowed EXCEPT ![r] = 1]
          /\ UNCHANGED <<incoming>>

(**********************************************************************)
(* Broadcast a message m to all replicas except the sender s.         *)
(**********************************************************************)
Broadcast(s, m) == [r \in Replica |-> 
                        IF s = r 
                        THEN incoming[s] 
                        ELSE incoming[r] (+) SetToBag({m})]

(**********************************************************************)
(* Replica r issues a Send() event, sending an update message.        *)
(**********************************************************************)
Send(r) == /\ sendAllowed[r] = 1
           /\ incoming' = Broadcast(r, vc[r])  \* broadcast vc[r] to other replicas
           /\ sendAllowed' = [sendAllowed EXCEPT ![r] = 0]
           /\ UNCHANGED <<vc, inc>>
   
(**********************************************************************)
(* Replica r issues a Receive() event, receiving an update message.   *)
(**********************************************************************)
SetMax(r, s) == IF r > s THEN r ELSE s
    
Receive(r) == /\ incoming[r] # EmptyBag \* there are accumulated increments from other replicas
              /\ \E m \in BagToSet(incoming[r]): \* message reordering can be tolerant
                    (/\ \A s \in Replica: vc' = [vc EXCEPT ![r][s] = SetMax(@, m[s])]
                     /\ incoming' = [incoming EXCEPT ![r] = @ (-) SetToBag({m})])  \* each message is delivered exactly once
              /\ sendAllowed' = [sendAllowed EXCEPT ![r] = 1]
              /\ UNCHANGED <<inc>>
-----------------------------------------------------------------------------
(**********************************************************************)
(* The Next-state relation.                                           *)
(**********************************************************************)
Next == /\ \E r \in Replica: Inc(r) \/ Send(r) \/ Receive(r)

(**********************************************************************)
(* The specification.                                                 *)
(**********************************************************************)
vars == <<vc, incoming, inc, sendAllowed>>
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

(**********************************************************************)
(* The correctness of counter:                                        *)
(* Eventual Convergence (EC), Quiescent Consistency (QC),             *)
(* and Strong Eventual Convergence (SEC).                             *)
(**********************************************************************)

-----------------------------------------------------------------------------
(**********************************************************************)
(* Eventual Consistency (EC)                                          *)
(* If clients stop issuing Incs,                                      *)
(* then the counters at all replicas will be eventually the same.     *)
(**********************************************************************)
Convergence == /\ \A r, s \in Replica: vc[r] = vc[s]
               /\ \E r, s \in Replica: vc[r][s] # 0 \* excluding the initial state
EC == <>Convergence

(**********************************************************************)
(* Quiescent Consistency (QC)                                         *)
(* If the system is at quiescent,                                     *)
(* then the counters at all replicas must be the same.                *)
(**********************************************************************)

AccBroadcast == \A r \in Replica: sendAllowed[r] = 0 \* all r \in Replica are not allowed to send
MessageDelivery == \A r \in Replica: incoming[r] = EmptyBag \* all messages have been delivered
QConvergence == \A r, s \in Replica: vc[r] = vc[s] \* no counter[r] # 0

QC == [](AccBroadcast /\ MessageDelivery => QConvergence)

(**********************************************************************)
(* Strong Eventual Consistency (SEC)                                  *)
(**********************************************************************)
                               
=============================================================================
\* Modification History
\* Last modified Sat Aug 11 11:49:53 CST 2018 by zfwang
\* Created Fri Aug 03 09:57:12 CST 2018 by zfwang
