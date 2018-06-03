----------------------------- MODULE PaxosStore -----------------------------
EXTENDS Integers, Naturals, FiniteSets, TLC

CONSTANTS Value,        \*the set of values
          Acceptor,     \*the set of Acceptors
          Quorum,       \*the set of majority sets of acceptors
          MCBallot        

Ballot == 0..MCBallot   \*the set of ballot numbers

Max(m, n) == IF m > n THEN m ELSE n

\*assumption of quorum to make the definition of quorum
ASSUME QuorumAssumption == /\ \A Q \in Quorum: Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum: Q1 \cap Q2 # {}

\* A value that not in Ballot for Phase1b of no value                 
None == CHOOSE v: v \notin Ballot

StateInTuple == [maxBal: Ballot \cup {-1},
                 maxVBal: Ballot \cup {-1},
                 maxVal: Value \cup {None}]


Message ==      [type: {"All"}, from: Acceptor]
           \cup [type: {"Return"}, from: Acceptor, to: Acceptor]
VARIABLES State,     \* State[X][Y]presents state Y from view of X
          msgs,      \* set of messages
          chosen
          
TypeOK == /\ State \in [Acceptor -> [Acceptor -> StateInTuple]]
          /\ msgs \in SUBSET Message
          /\ chosen \in SUBSET Value

vars == <<State, msgs, chosen>>
\*Init State
Init == /\ State = [a \in Acceptor |-> [b \in Acceptor |-> [maxBal |-> -1,
                                                            maxVBal |-> -1,
                                                            maxVal |-> None]]] 
        /\ msgs = {}
        /\ chosen = {}
 
Send(m) == msgs' = msgs \cup {m}
          
IssueM(a, b) == /\ State[a][a].maxBal < b
                /\ State' = [State EXCEPT ![a][a].maxBal = b]
                /\ Send([type |-> "All", from |-> a])                 
                /\ UNCHANGED chosen

IsMajority(a, b, Q) == \A a1 \in Q: State[a][a1].maxBal = b

FirstToIssueP(b) == \A a \in Acceptor: State[a][a].maxVBal # b
             
IssueP(a, b, v) == /\ State[a][a].maxBal = b
                   /\ State[a][a].maxVBal < b
                   /\ FirstToIssueP(b)
                   /\ \E Q \in Quorum: 
                      /\ IsMajority(a, b, Q)
                      /\ \/ \A a1 \in Q: State[a][a1].maxVal = None  
                         \/ \E s \in Value:
                            /\ s = v
                            /\ \E a2 \in Q: /\ State[a][a2].maxVal = s
                                            /\ \A a3 \in Q \ {a2}: State[a][a2].maxVBal \geq State[a][a3].maxVBal
                   /\ State' = [State EXCEPT ![a][a].maxVBal = b,
                                             ![a][a].maxVal = v]
                   /\ Send([type |-> "All", from |-> a])
                   /\ UNCHANGED chosen
 
OnMessage(a) == 
             /\ msgs # {}
             /\ \E m \in msgs:
                 \E from \in Acceptor:
                   /\ from = m.from
                   /\ \/ /\ m.type = "Return"
                         /\ m.to = a
                      \/ /\ m.type = "All"
                         /\ m.from # a
                   /\ LET maxval1 == Max(State[a][from].maxBal, State[from][from].maxBal)
                          maxval2 == Max(State[a][from].maxVBal, State[from][from].maxVBal)
                          maxval3 == Max(State[a][a].maxBal, State[from][from].maxBal)
                      IN  /\ IF State[a][from].maxVBal < maxval2 /\ State[a][a].maxBal =< State[from][from].maxVBal
                                THEN State' = [State EXCEPT ![a][from].maxBal = maxval1,
                                                            ![a][from].maxVBal = maxval2,
                                                            ![a][from].maxVal = State[from][from].maxVal,
                                                            ![a][a].maxBal = maxval3,
                                                            ![a][a].maxVBal = State[from][from].maxVBal,
                                                            ![a][a].maxVal = State[from][from].maxVal]
                                ELSE IF State[a][from].maxVBal < maxval2 /\ State[a][a].maxBal > State[from][from].maxVBal
                                     THEN State' = [State EXCEPT ![a][from].maxBal = maxval1,
                                                                 ![a][from].maxVBal = maxval2,
                                                                 ![a][from].maxVal = State[from][from].maxVal,
                                                                 ![a][a].maxBal = maxval3]
                                     ELSE IF State[a][from].maxVBal \geq maxval2 /\ State[a][a].maxBal =< State[from][from].maxVBal
                                          THEN State' = [State EXCEPT ![a][from].maxBal = maxval1,
                                                                      ![a][a].maxBal = maxval3,
                                                                      ![a][a].maxVBal = State[from][from].maxVBal,
                                                                      ![a][a].maxVal = State[from][from].maxVal]
                                          ELSE State' = [State EXCEPT ![a][from].maxBal = maxval1,
                                                                      ![a][a].maxBal = maxval3]
                          /\ IF State[a][a].maxBal < maxval3 \/ State[a][a].maxBal =< State[from][from].maxVBal
                                THEN \E Q \in Quorum, b \in Ballot, v \in Value:
                                       IF \A q \in Q: /\ State'[a][q].maxVBal = b
                                                     /\ State'[a][q].maxVal = v
                                          THEN chosen' = chosen \cup {v}
                                          ELSE UNCHANGED chosen
                                ELSE UNCHANGED chosen                                               
                   /\ IF State[from][a].maxBal < State[a][a].maxBal \/ State[from][a].maxVBal < State[a][a].maxVBal
                        THEN Send([type |-> "Return", from |-> a, to |-> from]) 
                        ELSE UNCHANGED msgs
                    
Next == \/ \E a \in Acceptor, b \in Ballot: IssueM(a, b)
        \/ \E a \in Acceptor, b \in Ballot, v \in Value: IssueP(a, b, v)
        \/ \E a \in Acceptor: OnMessage(a)                                
        
Spec == Init /\ [][Next]_vars

Nontriviality == chosen \subseteq Value
Consistency == Cardinality(chosen) =< 1  

LSpec == /\ Spec
         /\ \A a1, a2 \in Acceptor: /\ WF_vars(IssueM(a1, MCBallot) \/ IssueM(a2, MCBallot))
                                    /\ \A v \in Value: WF_vars(IssueP(a1, MCBallot, v) \/ IssueP(a2, MCBallot, v))
                                    /\ WF_vars(OnMessage(a1) \/ OnMessage(a2))
         
Liveness == <>(chosen # {})                            
=============================================================================
\* Modification History
\* Last modified Fri May 11 10:05:32 GMT+08:00 2018 by pure_
\* Last modified Wed May 02 11:37:23 CST 2018 by dell
\* Created Mon Apr 23 15:47:52 GMT+08:00 2018 by pure_
