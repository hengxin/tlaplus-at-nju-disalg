----------------------------- MODULE XJupiterH -----------------------------
(* 
XJupiterH: XJupiter with a history of all list states across the system.           
*)

EXTENDS XJupiter, TLCUtils
-------------------------------------------------------------
VARIABLE list
varsH == <<vars, list>>

TypeOKH == TypeOK /\ (list \subseteq List)
-------------------------------------------------------------
InitH == Init /\ list = {InitState}

DoH(c) == Do(c) /\ list' = list \cup {state'[c]}

RevH(c) == Rev(c) /\ list' = list \cup {state'[c]}

SRevH == SRev /\ list' = list \cup {state'[Server]}
-------------------------------------------------------------
NextH == 
    \/ \E c \in Client: DoH(c) \/ RevH(c)
    \/ SRevH
    
SpecH == InitH /\ [][NextH]_varsH /\ WF_varsH(NextH)
-------------------------------------------------------------
(*********************************************************************)
(* Weak List Consistency (WLSpec)                                    *)
(*********************************************************************)
ASSUME (TLCSet(1, <<"EmptyChannel", 0>>))
WLSpec == (comm!EmptyChannel /\ TLCCnt(1, 100))
            => \A l1, l2 \in list: 
                /\ Injective(l1) 
                /\ Injective(l2) 
                /\ Compatible(l1, l2)

THEOREM SpecH => WLSpec
(*********************************************************************)
(* Strong List Consistency (SLSpec)                                  *)
(*********************************************************************)
=============================================================================
\* Modification History
\* Last modified Sun Oct 14 11:08:39 CST 2018 by hengxin
\* Created Wed Oct 10 15:40:13 CST 2018 by hengxin