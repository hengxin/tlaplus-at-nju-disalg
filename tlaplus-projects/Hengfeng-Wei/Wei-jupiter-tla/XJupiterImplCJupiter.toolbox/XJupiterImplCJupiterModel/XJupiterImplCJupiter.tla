------------------------ MODULE XJupiterImplCJupiter ------------------------
(*
In this module, we show that XJupiter implements CJupiter.
To this end, we first extends XJupiter by replace its Cop with that used in CJupiter.
*)

EXTENDS XJupiterExtended

VARIABLES
    cincomingCJ, \* cincoming for CJupiter which contains original operations 
                 \* instead of transformed ones in XJupiter
    cxss \* cxss[c]: eXtra ss created during OT at the Server for client c \in Client

varsImpl == <<vars, cincomingCJ, cxss>>
    
(*
The Init predicate.
*)
InitImpl ==
    /\ Init
    /\ cincomingCJ = [c \in Client |-> <<>>]
    /\ cxss = [c \in Client |-> [node |-> {{}}, edge |-> {}]]

DoImpl(c) ==
    /\ Do(c)
    /\ UNCHANGED <<cincomingCJ, cxss>>

RevImpl(c) ==
    /\ Rev(c)
    /\ cincomingCJ[c] # <<>>  \* there are (original) operations to handle with
    /\ cincomingCJ' = [cincomingCJ EXCEPT ![c] = Tail(@)] \* also consume a message
    /\ UNCHANGED <<cxss>>

(*
Also broadcast the original operation to clients (using the cincomingCJ channels)
*)
SRevImpl == 
    /\ SRev
    /\ LET cop == [Head(sincoming) EXCEPT !.sctx = soids]
             c == cop.oid.c
            ss == xForm(cop, s2ss[c], scur[c], Remote)
        IN /\ cincomingCJ' = [cl \in Client |-> 
                                  IF cl = c
                                  THEN cincomingCJ[cl] 
                                  ELSE Append(cincomingCJ[cl], cop)]
           /\ cxss' = [cl \in Client |->
                        IF cl = c
                        THEN cxss[cl]
                        ELSE [cxss[cl] EXCEPT !.node = @ \cup Range(ss.node),
                                              !.edge = @ \cup Range(ss.edge)]]

(*
The next-state relation.
*)
NextImpl ==
    \/ \E c \in Client: DoImpl(c) \/ RevImpl(c)
    \/ SRevImpl

(*
The specification.
*)
SpecImpl == InitImpl /\ [][NextImpl]_varsImpl /\ WF_varsImpl(NextImpl) 

ss1 (+) ss2 ==
    [ss1 EXCEPT !.node = @ \cup ss2.node,
                !.edge = @ \cup ss2.edge]

IgnoreDir(ss) ==
    [ss EXCEPT !.edge = 
        \* [field \in (DOMAIN e \ {"lr"}) |-> e.field]
        {[from |-> e.from, to |-> e.to, cop |-> e.cop] : e \in @}]

CJ == INSTANCE CJupiter WITH 
        cincoming <- cincomingCJ, 
        css <- [r \in Replica |->
                    IF r = Server
                    THEN IgnoreDir(SetReduce((+), Range(s2ss), [node |-> {{}}, edge |-> {}])) 
                    ELSE IgnoreDir(c2ss[r] (+) cxss[r])],
        cur <- [r \in Replica |->
                    IF r = Server
                    \* It SHOULD be that Cardinality(Range(scur)) = 1
                    THEN CHOOSE n \in Range(scur) : TRUE 
                    ELSE ccur[r]]

THEOREM SpecImpl => CJ!Spec
=============================================================================
\* Modification History
\* Last modified Wed Oct 31 19:03:06 CST 2018 by hengxin
\* Created Fri Oct 26 15:00:19 CST 2018 by hengxin