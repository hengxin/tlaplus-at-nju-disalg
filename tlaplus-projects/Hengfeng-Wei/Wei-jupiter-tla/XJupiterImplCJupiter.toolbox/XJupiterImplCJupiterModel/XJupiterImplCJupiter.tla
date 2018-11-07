------------------------ MODULE XJupiterImplCJupiter ------------------------
(*
In this module, we show that XJupiter implements CJupiter.
To this end, we first extends XJupiter by replacing its Cop with that used in CJupiter.
*)

EXTENDS XJupiterExtended

VARIABLES
    op2ss,       \* a function from an operation (represented by its Oid) 
                 \* to the part of 2D state space produced while the operation is transformed
    c2ssX        \* c2ssX[c]: redundant (eXtra) 2D state space maintained for client c \in Client

varsImpl == <<varsEx, op2ss, c2ssX>>
-----------------------------------------------------------------------------
TypeOKImpl ==
    /\ TypeOKEx
    /\ \A oid \in DOMAIN op2ss: oid \in Oid /\ IsSS(op2ss[oid])
    /\ \A c \in Client: IsSS(c2ssX[c])
-----------------------------------------------------------------------------
InitImpl ==
    /\ InitEx
    /\ op2ss = <<>>
    /\ c2ssX = [c \in Client |-> [node |-> {{}}, edge |-> {}]]
-----------------------------------------------------------------------------
(*
Client c \in Client generates an operation.
*)
DoImpl(c) ==
    /\ DoEx(c)
    /\ UNCHANGED <<op2ss, c2ssX>>

ss1 (+) ss2 ==
    [ss1 EXCEPT !.node = @ \cup ss2.node,
                !.edge = @ \cup ss2.edge]
(*
Client c \in Client receives a message from the Server.
*)
RevImpl(c) ==
    /\ RevEx(c)
    /\ LET cop == Head(cincoming[c])
        IN c2ssX' = [c2ssX EXCEPT ![c] = @ (+) op2ss[cop.oid]]
    /\ UNCHANGED <<op2ss>>
(*
The Server receives a message.
*)
SRevImpl == 
    /\ SRevEx
    /\ LET cop == Head(sincoming)
             c == cop.oid.c
            ss == xForm(cop, s2ss[c], scur[c], Remote)
        IN op2ss' = op2ss @@ (cop.oid :> [node |-> Range(ss.node), edge |-> Range(ss.edge)])
    /\ UNCHANGED <<c2ssX>>
-----------------------------------------------------------------------------
NextImpl ==
    \/ \E c \in Client: DoImpl(c) \/ RevImpl(c)
    \/ SRevImpl

SpecImpl == InitImpl /\ [][NextImpl]_varsImpl 
    /\ WF_varsImpl(SRevImpl \/ \E c \in Client: RevImpl(c)) 

(*
Ignore the lr field in edges of 2D state space.
*)
IgnoreDir(ss) ==
    [ss EXCEPT !.edge = 
        \* {[field \in (DOMAIN e \ {"lr"}) |-> e.field] : e \in @}]
        {[from |-> e.from, to |-> e.to, cop |-> e.cop] : e \in @}]

CJ == INSTANCE CJupiter 
        WITH cincoming <- cincomingCJ, 
             css <- [r \in Replica |-> 
                        IF r = Server 
                        THEN IgnoreDir(SetReduce((+), Range(s2ss), [node |-> {{}}, edge |-> {}])) 
                        ELSE IgnoreDir(c2ss[r] (+) c2ssX[r])], 
             cur <- [r \in Replica |-> 
                        IF r = Server 
                        \* It SHOULD be that Cardinality(Range(scur)) = 1 
                        THEN CHOOSE n \in Range(scur) : TRUE 
                        ELSE ccur[r]]

THEOREM SpecImpl => CJ!Spec
=============================================================================
\* Modification History
\* Last modified Wed Nov 07 11:16:30 CST 2018 by hengxin
\* Created Fri Oct 26 15:00:19 CST 2018 by hengxin