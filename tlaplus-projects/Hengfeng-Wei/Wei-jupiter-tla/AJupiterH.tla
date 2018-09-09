----------------------------- MODULE AJupiterH -----------------------------
(***************************************************************************)
(* AJupiter with a history of all list states across the system.           *)
(***************************************************************************)

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
    
SpecH == InitH /\ [][NextH]_varsH /\ WF_varsH(NextH)
-------------------------------------------------------------
(*********************************************************************)
(* Weak List Consistency (WLSpec)                                    *)
(*********************************************************************)
WLSpec == comm!EmptyChannel 
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
\* Last modified Sun Sep 09 10:35:07 CST 2018 by hengxin
\* Created Thu Aug 30 21:26:18 CST 2018 by hengxin