----------------------------- MODULE XJupiterSS -----------------------------

(*
Note: This spec has been deprecated. 
It has done a simple task in a rather complicated way.done 
See the CSSync property defined in XJupiter.

Specification of XJupiter with properties about 2D state spaces.
*)

EXTENDS XJupiter

VARIABLES
    roid    \* roid[r]: the set of operations, represented by their oids, 
            \* that have been processed by replica r \in Replica
            
varsSS == <<vars, roid>>

TypeOKSS == 
    /\ TypeOK 
    /\ roid \subseteq Oid

InitSS == 
    /\ Init
    /\ [r \in Replica |-> {}]
    
DoSS(c) ==
    /\ Do(c)
    /\ roid' = [roid EXCEPT ![c] = @ \cup {[c |-> c, seq |-> cseq'[c]]}]
    
RevSS(c) ==
    /\ Rev(c)
    /\ UNCHANGED <<roid>>

SRevSS ==
    /\ SRev
    /\ LET cop == Head(sincoming)
        IN roid' = [roid EXCEPT ![Server] = @ \cup {cop.oid}]    
-----------------------------------------------------------------------------
(* 
The next-state relation.
*)
NextSS == 
    \/ \E c \in Client: DoSS(c) \/ RevSS(c)
    \/ SRevSS
(* 
The SpecSS.  (TODO: Check the fairness condition.)
*)
SpecSS == InitSS /\ [][NextSS]_varsSS /\ WF_vars(NextSS)
=============================================================================
\* Modification History
\* Last modified Thu Oct 11 18:00:45 CST 2018 by hengxin
\* Created Thu Oct 11 17:38:47 CST 2018 by hengxin