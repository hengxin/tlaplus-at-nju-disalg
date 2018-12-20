------------------------------ MODULE XJupiter ------------------------------
(*
Specification of the Jupiter protocol described in CSCW'2014 
by Yi Xu, Chengzheng Sun, and Mo Li.
We call it XJupiter, with 'X' for "Xu".
*)
EXTENDS JupiterCtx, GraphsUtil
-----------------------------------------------------------------------------
VARIABLES
    (*
      The 2D state spaces (ss, for short).
      Each client maintains one 2D state space.
      The server maintains n 2D state spaces, one for each client.
    *)
    c2ss,   \* c2ss[c]: the 2D state space at client c \in Client
    s2ss    \* s2ss[c]: the 2D state space maintained by the Server for client c \in Client

vars == <<intVars, ctxVars, c2ss, s2ss>>
-----------------------------------------------------------------------------
(*
Direction flags for edges in 2D state spaces and OT.
*)
Local == 0 
Remote == 1
(* 
A 2D state space is a directed graph with labeled edges.
It is represented by a record with node field and edge field.
Each node is characterized by its context, a set of operations.
Each edge is labeled with an operation 
and a direction flag indicating whether this edge is LOCAL or REMOTE.
For clarity, we denote edges by records instead of tuples.
*)
IsSS(G) ==
    /\ G = [node |-> G.node, edge |-> G.edge]
    /\ G.node \subseteq (SUBSET Oid)
    /\ G.edge \subseteq [from: G.node, to: G.node, cop: Cop, lr: {Local, Remote}]

TypeOK == 
    /\ TypeOKInt
    /\ TypeOKCtx
    /\ Comm(Cop)!TypeOK
    /\ \A c \in Client: IsSS(c2ss[c]) /\ IsSS(s2ss[c])
-----------------------------------------------------------------------------
Init == 
    /\ InitInt
    /\ InitCtx
    /\ Comm(Cop)!Init
    /\ c2ss = [c \in Client |-> EmptyGraph]
    /\ s2ss = [c \in Client |-> EmptyGraph]
-----------------------------------------------------------------------------
(* 
Locate the node in the 2D state space ss which matches the context ctx of cop.    
*)
Locate(cop, ss) == CHOOSE n \in ss.node : n = cop.ctx
(* 
xForm: iteratively transform cop with a path
through the 2D state space ss at some client, 
following the edges with the direction flag d.
*)
xForm(cop, ss, current, d) ==
    LET u == Locate(cop, ss)
        v == u \cup {cop.oid}
        RECURSIVE xFormHelper(_, _, _, _, _)
        \* 'h' stands for "helper"; xss: eXtra ss created during transformation
        xFormHelper(uh, vh, coph, xss, xcoph) ==  
            IF uh = current
            THEN <<xss, xcoph>>
            ELSE LET e == CHOOSE e \in ss.edge: e.from = uh /\ e.lr = d
                     uprime == e.to
                     copprime == e.cop
                     coph2copprime == COT(coph, copprime)
                     copprime2coph == COT(copprime, coph)
                     vprime == vh \cup {copprime.oid}
                  IN xFormHelper(uprime, vprime, coph2copprime,
                        [node |-> xss.node \cup {vprime}, 
                         edge |-> xss.edge \cup {[from |-> vh, to |-> vprime, cop |-> copprime2coph, lr |-> d], 
                                    [from |-> uprime, to |-> vprime, cop |-> coph2copprime, lr |-> 1 - d]}],
                                 coph2copprime)
    IN xFormHelper(u, v, cop, [node |-> {v}, edge |-> {[from |-> u, to |-> v, cop |-> cop, lr |-> 1 - d]}], cop)
-----------------------------------------------------------------------------
(* 
Client c \in Client perform operation cop guided by the direction flag d.
*)
ClientPerform(cop, c, d) ==
    LET xform == xForm(cop, c2ss[c], ds[c], d) \* xform: <<xss, xcop>>
          xss == xform[1]
         xcop == xform[2]
    IN /\ c2ss' = [c2ss EXCEPT ![c] = @ (+) xss]
       /\ state' = [state EXCEPT ![c] = Apply(xcop.op, @)]
(* 
Client c \in Client generates an operation op.
*)
DoOp(c, op) == 
    LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq'[c]], ctx |-> ds[c]] 
        IN /\ ClientPerform(cop, c, Remote)
           /\ UpdateDS(c, cop)
           /\ Comm(Cop)!CSend(cop)

DoIns(c) ==
    \E ins \in {op \in Ins: op.pos \in 1 .. (Len(state[c]) + 1) /\ op.ch \in chins /\ op.pr = Priority[c]}:
        /\ DoOp(c, ins)
        /\ chins' = chins \ {ins.ch} \* We assume that all inserted elements are unique.

DoDel(c) == 
    \E del \in {op \in Del: op.pos \in 1 .. Len(state[c])}:
        /\ DoOp(c, del)
        /\ UNCHANGED chins

Do(c) == 
    /\ DoCtx(c)
    /\ \/ DoIns(c) 
       \/ DoDel(c)
    /\ UNCHANGED s2ss
(* 
Client c \in Client receives a message from the Server.
*)
Rev(c) == 
    /\ Comm(Cop)!CRev(c)
    /\ LET cop == Head(cincoming[c]) \* the received (transformed) operation
        IN ClientPerform(cop, c, Local)
    /\ RevCtx(c)
    /\ UNCHANGED <<chins, s2ss>>
-----------------------------------------------------------------------------
(*
The Server performs operation cop.
*)
ServerPerform(cop) == 
    LET c == cop.oid.c
     scur == ds[Server]
    xform == xForm(cop, s2ss[c], scur, Remote) \* xform: <<xss, xcop>>
      xss == xform[1]
     xcop == xform[2]
     xcur == scur \cup {cop.oid}
    IN /\ s2ss' = [cl \in Client |-> 
                    IF cl = c 
                    THEN s2ss[cl] (+) xss
                    ELSE s2ss[cl] (+) [node |-> {xcur}, 
                                       edge |-> {[from |-> scur, to |-> xcur, 
                                                   cop |-> xcop, lr |-> Remote]}]
                  ]
       /\ state' = [state EXCEPT ![Server] = Apply(xcop.op, @)]
       /\ Comm(Cop)!SSendSame(c, xcop)  \* broadcast the transformed operation
(* 
The Server receives a message.
*)
SRev == 
    /\ Comm(Cop)!SRev
    /\ LET cop == Head(sincoming)
        IN ServerPerform(cop)
    /\ SRevCtx
    /\ UNCHANGED <<chins, c2ss>>
-----------------------------------------------------------------------------
Next == 
    \/ \E c \in Client: Do(c) \/ Rev(c)
    \/ SRev

Fairness == 
    WF_vars(SRev \/ \E c \in Client: Rev(c))

Spec == Init /\ [][Next]_vars \* /\ Fairness
-----------------------------------------------------------------------------
(*
In Jupiter (not limited to XJupiter), each client synchronizes with the server.
In XJupiter, this is expressed as the following CSSync property.
*)
CSSync == 
    \forall c \in Client: (ds[c] = ds[Server]) => c2ss[c] = s2ss[c]
=============================================================================
\* Modification History
\* Last modified Wed Dec 19 11:41:44 CST 2018 by hengxin
\* Created Tue Oct 09 16:33:18 CST 2018 by hengxin