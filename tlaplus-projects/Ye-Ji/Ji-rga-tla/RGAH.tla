-------------------------------- MODULE RGAH --------------------------------
EXTENDS RGA,SequenceUtils
-----------------------------------------------------------------------------
VARIABLE list

varsH == <<vars, list>>

TypeOKH == TypeOK /\ (list \in SUBSET List)
-----------------------------------------------------------------------------
InitH == Init /\ list = {}

DoH(r) == Do(r) /\ list' = list \cup   { Readtree2list(rtree[r]',"o",rtomb[r]',{}) }

SendH(r) == Send(r) /\ list' = list

ReceiveH(r) == Receive(r) /\ list' = list \cup  { Readtree2list(rtree[r]',"o",rtomb[r]',{}) }
-----------------------------------------------------------------------------
NextH == 
   \E r \in Replica: DoH(r) \/ SendH(r) \/ ReceiveH(r)
-----------------------------------------------------------------------------   
SpecH == InitH /\ [][NextH]_varsH
-----------------------------------------------------------------------------  
(*
Weak List Consistency 
*)
WLSpec ==  \A l1, l2 \in list: 
                /\ Injective(l1) 
                /\ Injective(l2) 
                /\ Compatible(l1, l2)
(*
Strong List Consistency 
*)                
SLSpec ==   /\ WLSpec
            /\ \A l1, l2,l3 \in list: 
                 nocylce(l1, l2, l3)                    
=============================================================================
\* Modification History
\* Last modified Sat Dec 15 21:10:45 CST 2018 by xhdn
\* Last modified Sat Dec 15 12:40:54 CST 2018 by xhdn
\* Last modified Thu Dec 13 17:02:14 CST 2018 by jywellin
\* Created Wed Dec 05 18:11:55 CST 2018 by jywellin
