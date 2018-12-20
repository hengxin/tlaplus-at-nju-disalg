-------------------------------- MODULE RGA --------------------------------
EXTENDS Integers,Sequences,Naturals,TLC,InsertTree
-----------------------------------------------------------------------------
CONSTANTS Replica       
-----------------------------------------------------------------------------        
VARIABLES rtree,rtomb,rinsbuf,rtombbuf,rins_incoming,rtomb_incoming,chins,tcurrent
vars == <<rtree,rtomb,rinsbuf,rtombbuf,rins_incoming,rtomb_incoming,chins,tcurrent>>
-----------------------------------------------------------------------------
List == Seq(Char) 

Inscomm == INSTANCE P2PComm WITH  incoming <- rins_incoming,outbuf <- rinsbuf
                               
Tombcomm == INSTANCE P2PComm WITH  incoming <- rtomb_incoming,outbuf <- rtombbuf                          
-----------------------------------------------------------------------------
TypeOK == /\ tcurrent \in 1..Charnum + 1
          /\ rtomb \in [Replica -> SUBSET Char]
          /\ rtombbuf \in [Replica -> SUBSET Char]
          /\ rtomb_incoming \in [Replica -> SUBSET Char]
          /\ chins \in SUBSET Char
          /\ rtree \in [Replica -> SUBSET node]
          /\ rinsbuf \in [Replica -> SUBSET node]
          /\ rins_incoming \in [Replica -> SUBSET node]
-----------------------------------------------------------------------------         
                      
Init == 
    /\ Inscomm!Init
    /\ Tombcomm!Init
    /\ rtree = [r \in Replica |-> {}]
    /\ rtomb = [r \in Replica |-> {}]
    /\ chins = Char
    /\ tcurrent = 1

    
DoIns(r) ==
    \E ins \in node:
        /\ ins.father \in Readtree2set(rtree[r]) \cup {"o"}
        /\ ins.time  = tcurrent
        /\ tcurrent' = tcurrent + 1
        /\ ins.ch \in chins
        /\ chins' = chins \ {ins.ch} 
        /\ rtree' =  [rtree  EXCEPT![r] = @ \cup {ins}] 
        /\ rinsbuf' = [rinsbuf EXCEPT![r] = @ \cup {ins}] 
        /\ UNCHANGED <<rtomb,rtombbuf,rins_incoming,rtomb_incoming>>


DoDel(r) == 
    \E del \in Char:
        /\ del \in Readtree2set(rtree[r])
        /\ ~ del \in rtomb[r]
        /\ rtomb' = [rtomb EXCEPT ![r] = @ \cup {del}] 
        /\ rtombbuf' = [rtombbuf EXCEPT ![r] = @ \cup {del}] 
        /\ UNCHANGED <<chins, tcurrent, rtree, rinsbuf,rins_incoming,rtomb_incoming>>
(* 
do transitions
*)     
Do(r) == 
    \/ DoIns(r)
    \/ DoDel(r)

(* 
send transitions
*)     
Send(r) ==
    \/ /\ Inscomm!Send(r)
       /\ UNCHANGED <<chins, tcurrent,rtree,rtomb,rtombbuf,rtomb_incoming>>
    \/ /\ Tombcomm!Send(r)
       /\ UNCHANGED <<chins, tcurrent,rtree,rtomb,rinsbuf,rins_incoming>>

(* 
receive transitions
*)
Receive(r) ==
    /\ \/ /\ Inscomm!Receive(r)
          /\ UNCHANGED <<rtomb_incoming,rtombbuf>>
       \/ /\ Tombcomm!Receive(r)
          /\ UNCHANGED <<rins_incoming,rinsbuf>>
    /\ rtree' =  [rtree  EXCEPT![r] = @ \cup rins_incoming[r]] 
    /\ rtomb' = [rtomb EXCEPT ![r] = @ \cup rtomb_incoming[r]]
    /\ UNCHANGED <<chins, tcurrent>> 
-----------------------------------------------------------------------------
Next == 
   \E r \in Replica: Do(r) \/ Send(r)\/ Receive(r)

-----------------------------------------------------------------------------                   
Spec == Init /\ [][Next]_vars   
 
-----------------------------------------------------------------------------
(*
eventual consistency              
*)
EC ==  Inscomm!EmptyChannel /\  Tombcomm!EmptyChannel => 
            \A r1,r2  \in Replica:
                 Readtree2list(rtree[r1],"o",rtomb[r1],{})= Readtree2list(rtree[r2],"o",rtomb[r2],{})
                                
=============================================================================
\* Modification History
\* Last modified Tue Dec 18 00:47:48 CST 2018 by xhdn
\* Last modified Sat Dec 15 21:05:43 CST 2018 by xhdn
\* Last modified Wed Dec 12 21:27:49 CST 2018 by jywellin
\* Last modified Tue Dec 04 21:42:36 CST 2018 by jywellin
\* Last modified Mon Dec 03 15:01:06 CST 2018 by xhdn
\* Last modified Wed Nov 28 22:07:24 CST 2018 by jywellin
\* Created Tue Nov 06 15:55:23 CST 2018 by xhdn
