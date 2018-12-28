----------------------------- MODULE CJupiterH -----------------------------
(*
CJupiter with a history of all list states across the system.
*)
EXTENDS CJupiter
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
    
SpecH == InitH /\ [][NextH]_varsH /\ WF_varsH(SRevH \/ \E c \in Client: RevH(c))
-------------------------------------------------------------
(*
WLSpec: the weak list specification 
*)
WLSpec == Comm(Cop)!EmptyChannel 
            => \A l1, l2 \in list: 
                /\ Injective(l1) 
                /\ Injective(l2) 
                /\ Compatible(l1, l2)

THEOREM SpecH => WLSpec
(*
SLSpec: the strong list specification
*)
=============================================================================
\* Modification History
\* Last modified Tue Dec 04 21:14:37 CST 2018 by hengxin
\* Created Tue Oct 09 09:28:48 CST 2018 by hengxin