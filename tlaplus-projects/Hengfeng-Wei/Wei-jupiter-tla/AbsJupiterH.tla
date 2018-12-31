---------------------------- MODULE AbsJupiterH ----------------------------
(*
AbsJupiter with a history of all list states across the system.
*)
EXTENDS AbsJupiter 
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

FairnessH ==
    WF_varsH(SRevH \/ \E c \in Client: RevH(c))
    
SpecH == InitH /\ [][NextH]_varsH \* /\ FairnessH
-------------------------------------------------------------
WLSpec == \* the weak list specification 
    Comm(Cop)!EmptyChannel 
        => \A l1, l2 \in list: 
            /\ Injective(l1) 
            /\ Injective(l2) 
            /\ Compatible(l1, l2)

THEOREM SpecH => WLSpec
=============================================================================
\* Modification History
\* Last modified Mon Dec 31 18:56:37 CST 2018 by hengxin
\* Created Sat Dec 15 09:00:46 CST 2018 by hengxin
