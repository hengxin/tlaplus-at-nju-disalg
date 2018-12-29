----------------------------- MODULE AJupiterH -----------------------------
EXTENDS AJupiter
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
(*********************************************************************)
(* Weak List Consistency (WLSpec)                                    *)
(*********************************************************************)
WLSpec == Comm(Msg)!EmptyChannel 
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
\* Last modified Thu Dec 27 20:36:24 CST 2018 by hengxin
\* Created Thu Aug 30 21:26:18 CST 2018 by hengxin