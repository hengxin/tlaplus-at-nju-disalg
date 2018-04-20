---------------------------- MODULE ClassicPaxos ----------------------------
EXTENDS Integers, Naturals, FiniteSets

CONSTANTS Value,        \*the set of values
          Acceptor,     \*the set of Acceptors
          Quorum,       \*the set of majority sets of acceptors
          MCBallot        \*the set of ballot numbers

Ballot == 0..MCBallot

\*assumption of quorum to make the definition of quorum
ASSUME QuorumAssumption == /\ \A Q \in Quorum: Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum: Q1 \cap Q2 # {}
          
\* A value that not in Ballot for Phase1b of no value                 
None == CHOOSE v: v \notin Ballot

\*All messages that disappers in the algorithm
Message ==       [type: {"1a"}, bal: Ballot]
            \cup [type: {"1b"}, acc: Acceptor, bal: Ballot, mBal: Ballot \cup {-1}, mVal: Value \cup {None}]
            \cup [type: {"2a"}, bal: Ballot, val: Value]
            \cup [type: {"2b"}, acc: Acceptor, bal: Ballot, val: Value]

VARIABLE maxBal,    \* max prepare request that a has responded
         maxVBal,   \* <<maxVBal[a], maxVal[a]>> is the vote with the largest
         maxVal,    \* ballot number cast by a; it equals <<-1, None>> if
                    \* a has not cast any vote.
         msgs       \* The set of all messages that have been sent.
          
\*the tuple of all variables
vars == <<maxBal, maxVBal, maxVal, msgs>>
--------------------------------------------------------------------------
\*the initial state          
Init == /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVal = [a \in Acceptor |-> None]
        /\ msgs = {}
----------------------------------------------------------------------------
Send(m) == msgs' = msgs \cup {m}
(***************************************************************************)
(* send prepare request                                                    *)
(***************************************************************************)
Phase1a(b) == /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* acceptor a respond to prepare request of m in msgs                      *)
(***************************************************************************)              
Phase1b(a) == /\ \E m \in msgs:
                 /\ m.type = "1a"
                 /\ m.bal > maxBal[a]
                 /\ maxBal' = [maxBal EXCEPT ![a]= m.bal]
                 /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, mBal |-> maxVBal[a], mVal |-> maxVal[a]])
              /\ UNCHANGED <<maxVBal, maxVal>>
(***************************************************************************)
(* two necessary condition:                                                *)
(*                (i) leader in ballot b has not started phase2a           *)
(*                (ii) there exits a majority of acceptors that accepts.   *)
(***************************************************************************)
Phase2a(b, v) == /\ ~ \E m \in msgs: m.type = "2a" /\ m.bal = b
                 /\ \E Q \in Quorum:
                    LET Q1b == {m \in msgs : /\ m.type = "1b"
                                             /\ m.acc \in Q
                                             /\ m.bal = b}
                        Q1bv == {m \in Q1b : m.mBal \geq 0}
                    IN /\ \A a \in Q : \E m \in Q1b : m.acc = a 
                       /\ \/ Q1bv = {}
                          \/ \E m \in Q1bv : 
                             /\ m.mVal = v
                             /\ \A mm \in Q1bv : m.mBal \geq mm.mBal
                 /\ Send([type |-> "2a", bal |-> b, val |-> v])
                 /\ UNCHANGED <<maxBal, maxVBal, maxVal>> 
(***************************************************************************)
(* acceptor a accepts the acceptr request of(n, v), update the maxBal,     *)
(* maxVal and maxVBal.                                                     *)
(***************************************************************************)
Phase2b(a) == /\ \E m \in msgs:
                 /\ m.type = "2a"
                 /\ m.bal \geq maxBal[a]
                 /\ maxBal' = [maxBal EXCEPT ![a] = m.bal] 
                 /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal] 
                 /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
                 /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])
(***************************************************************************)
(* votes describing for the vote accepts by the acceptor in the phase2b    *)
(***************************************************************************)
votes == [a \in Acceptor |->  {<<m.bal, m.val>> : m \in {mm \in msgs: /\ mm.type = "2b"
                                                                      /\ mm.acc = a }}]
\* Acceptor a accepted (b, v)
VotedFor(a, b, v) == <<b, v>> \in votes[a]

\* Acceptor a not accepted any value in ballot b
DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v) 

\* v has been chosen
ChosenAt(b, v) == \E Q \in Quorum : 
                     \A a \in Q : VotedFor(a, b, v)  
\* the set of value learner to learn || value has been chosen
chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

\* every acceptor can only vote for one value at a ballot                            
OneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
       VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)
      
\* Acceptor a has not and will never cast a vote in ballot b
CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)
(*************************************************************************)
(* no value other than v can be chosen.                                  *) 
(* If this is true, then ChosenAt(b, w) is not and can never become true *)
(* for any w # v.                                                        *)
(*************************************************************************)
NoneOtherChoosableAt(b, v) == 
   \E Q \in Quorum :
     \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)
(*************************************************************************)
(* If this is true, then no value other than v has been or can ever be   *)
(* chosen in any ballot numbered less than b.                            *)
(*************************************************************************)
SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
                 VotedFor(a, b, v) => SafeAt(b, v)

ShowsSafeAt(Q, b, v) == /\ \A a \in Q : maxBal[a] \geq b
                        /\ \E c \in -1..(b-1) : 
                           /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
                           /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)  

-----------------------------------------------------------------------------
(***************************************************************************)
(* check safety: (i) No value has been chosen unless it is first proposed  *)
(*               (ii) most single value has been chosen                    *)
(***************************************************************************)
TypeOK == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVal \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message
          /\ chosen \subseteq Value
          /\ IsFiniteSet(chosen)
          /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
\* Invariant
Inv == /\ TypeOK
       /\ \A a \in Acceptor : IF maxVBal[a] = -1
                                THEN maxVal[a] = None
                                ELSE <<maxVBal[a], maxVal[a]>> \in votes[a] 
       /\ \A m \in msgs : 
             /\ (m.type = "1b") => /\ maxBal[m.acc] \geq m.bal
                                   /\ (m.mBal \geq 0) =>  
                                       <<m.mBal, m.mVal>> \in votes[m.acc]
             /\ (m.type = "2a") => /\ \E Q \in Quorum : 
                                         ShowsSafeAt(Q, m.bal, m.val)
                                   /\ \A mm \in msgs : /\ mm.type = "2a"
                                                       /\ mm.bal = m.bal
                                                       => mm.val = m.val                                                                     
       /\ OneValuePerBallot
       /\ Cardinality(chosen) \leq 1
       /\ VotesSafe

\* the definition of next state and spec
Next == \/ \E b \in Ballot : \/ Phase1a(b)
                             \/ \E v \in Value : Phase2a(b, v)
        \/ \E a \in Acceptor : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* check liveness:                                                         *)
(***************************************************************************)
MCLSpec == /\ Spec 
           /\ WF_vars(Phase1a(MCBallot))
           /\ \A v \in Value : WF_vars(Phase2a(MCBallot,v))
           /\ \A a1, a2 \in Acceptor: WF_vars(Phase1b(a1) \/ Phase2b(a1) \/ Phase1b(a2) \/ Phase2b(a2))

MCLiveness == <>(chosen # {})          
-----------------------------------------------------------------------------
=============================================================================
\* Modification History
\* Last modified Fri Apr 20 13:16:50 GMT+08:00 2018 by pure_
\* Created Fri Apr 13 19:17:28 GMT+08:00 2018 by pure_
