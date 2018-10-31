------------------------ MODULE XJupiterImplCJupiter ------------------------
(*
In this module, we show that XJupiter implements CJupiter.
To this end, we first extends XJupiter by replace its Cop with that used in CJupiter.
*)

EXTENDS XJupiterExtended

VARIABLES
    cincomingCJ
    
InitImpl ==
    /\ Init
    /\ cincomingCJ = [c \in Client |-> <<>>]

\* SpecImpl == InitImpl /\ [][NextImpl]_varsImpl  \* +liveness
\* CJ == INSTANCE CJupiter WITH soids <- soids
\* THEOREM SpecImpl => CJ!Spec
=============================================================================
\* Modification History
\* Last modified Wed Oct 31 10:58:49 CST 2018 by hengxin
\* Created Fri Oct 26 15:00:19 CST 2018 by hengxin