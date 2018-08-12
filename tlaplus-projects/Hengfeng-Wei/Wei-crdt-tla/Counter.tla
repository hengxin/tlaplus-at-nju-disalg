------------------------------ MODULE Counter ------------------------------

(**********************************************************************)
(* TLA+ module for Op-based Counter.                                  *)
(* See its implementation in paper Burckhardt@POPL'2014.              *)
(* We check that the Op-based Counter satisfies the                   *)
(* strong eventual convergence property (SEC)                         *)
(**********************************************************************)

EXTENDS Naturals, Sequences, Bags, TLC

CONSTANTS
    (**********************************************************************)
    (* Protocol variables.                                                *)
    (**********************************************************************)
    Replica, \* the set of replicas
    (**********************************************************************)
    (* Auxiliary variables for model checking.                            *)
    (**********************************************************************)
    Max      \* Max[r]: the maximum number of the Inc() event replica r \in Replica can issue; for finite-state model checking
    
VARIABLES
    (**********************************************************************)
    (* Protocol variables.                                                *)
    (**********************************************************************)
    counter,    \* counter[r]: the current value of the counter at replica r \in Replica
    acc,        \* acc[r]: the number of increments performed since the last broadcast at replica r \in Replica
    incoming,   \* incoming[r]: incoming messages at replica r \in Replica
    (**********************************************************************)
    (* Auxiliary variables for model checking.                            *)
    (**********************************************************************)
    inc         \* inc[r]: the number of Inc() events issued by the replica r \in Replica; for finite-state model checking

(**********************************************************************)
(* The type correctness predicate.                                    *)
(**********************************************************************)
TypeOK == /\ counter \in [Replica -> Nat]
          /\ acc \in [Replica -> Nat]
          \* /\ incoming \in [Replica -> SubBag(SetToBag(Nat))] \* message ordering is not important; using bag (i.e., multiset)
          /\ inc \in [Replica -> Nat]

--------------------------------------------------------------------------------
(**********************************************************************)
(* The initial state predicate.                                       *)
(**********************************************************************)
Init == /\ counter = [r \in Replica |-> 0]
        /\ acc = [r \in Replica |-> 0]
        /\ incoming = [r \in Replica |-> EmptyBag]
        /\ inc = [r \in Replica |-> 0]

--------------------------------------------------------------------------------
(**********************************************************************)
(* Replica r \in Replica issues an Inc() event.                       *)
(**********************************************************************)
Inc(r) == /\ TRUE   \* no pre-condition
          /\ counter' = [counter EXCEPT ![r] = @ + 1]    \* current counter + 1
          /\ acc' = [acc EXCEPT ![r] = @ + 1]   \* # of accumulated increments + 1
          /\ inc' = [inc EXCEPT ![r] = @ + 1]   \* # of increments + 1
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
Send(r) == /\ acc[r] # 0    \* there are accumulated increments
           /\ acc' = [acc EXCEPT ![r] = 0]  \* reset acc[r]
           /\ incoming' = Broadcast(r, acc[r])  \* broadcast acc[r] to other replicas
           /\ UNCHANGED <<counter, inc>> 

(**********************************************************************)
(* Replica r issues a Receive() event, receiving an update message.   *)
(**********************************************************************)
Receive(r) == /\ incoming[r] # EmptyBag \* there are accumulated increments from other replicas
              /\ \E m \in BagToSet(incoming[r]): \* message reordering can be tolerant
                    (/\ counter' = [counter EXCEPT ![r] = @ + m]
                     /\ incoming' = [incoming EXCEPT ![r] = @ (-) SetToBag({m})])  \* each message is delivered exactly once
              /\ UNCHANGED <<acc, inc>>

--------------------------------------------------------------------------------
(**********************************************************************)
(* The Next-state relation.                                           *)
(**********************************************************************)
Next == /\ \E r \in Replica: Inc(r) \/ Send(r) \/ Receive(r)
              
(**********************************************************************)
(* The specification.                                                 *)
(**********************************************************************)
vars == <<counter, acc, incoming, inc>>
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

--------------------------------------------------------------------------------
(**********************************************************************)
(* A state constraint that is useful for validating the specification *)
(* using finite-state model checking:                                 *)
(* each replica r \in Replica can issue at most Max[r] Inc() events.  *)
(**********************************************************************)
IncConstraint == \A r \in Replica: inc[r] <= Max[r]

--------------------------------------------------------------------------------
(**********************************************************************)
(* The correctness of counter:                                        *)
(* Eventual Convergence (EC), Quiescent Consistency (QC),             *)
(* and Strong Eventual Convergence (SEC).                             *)
(**********************************************************************)


(**********************************************************************)
(* Eventual Consistency (EC)                                          *)
(**********************************************************************)
Convergence == \A r, s \in Replica: (counter[r] = counter[s] /\ counter[r] # 0) \* counter[r] # 0: excluding the initial state
EC == <>Convergence

(**********************************************************************)
(* Quiescent Consistency (QC)                                         *)
(**********************************************************************)
AccBroadcast == \A r \in Replica: acc[r] = 0    \* all accumulated increments have been broadcast
MessageDelivery == \A r \in Replica: incoming[r] = EmptyBag \* all messages have been delivered
QConvergence == \A r, s \in Replica: counter[r] = counter[s] \* no counter[r] # 0

QC == []((AccBroadcast /\ MessageDelivery) => QConvergence)

(**********************************************************************)
(* Strong Eventual Consistency (SEC)                                         *)
(**********************************************************************)
=============================================================================
\* Modification History
\* Last modified Thu Aug 02 15:02:12 CST 2018 by hengxin
\* Created Sun Jun 03 20:08:57 CST 2018 by hengxin