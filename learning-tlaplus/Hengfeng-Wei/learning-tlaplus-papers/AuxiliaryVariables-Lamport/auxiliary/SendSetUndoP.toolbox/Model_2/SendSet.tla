------------------------------ MODULE SendSet ------------------------------
(***************************************************************************)
(* This module and modules SendSetUndo and SendSetUndoP are the            *)
(* specifications in Section 4.3 of the paper "Auxiliary Variables in      *)
(* TLA+".                                                                  *)
(*                                                                         *)
(* This module specifies a system in which a sender sends data values in   *)
(* an unspecified set Data to a receiver.  A data value d is sent by       *)
(* setting the variable x to d, and it is received by setting x to a value *)
(* NotData that is not an element of Data.  The sender maintains a set y   *)
(* of data values that is has chosen to send.  The sender's actions are    *)
(* `Choose', which adds to y an arbitrary data value not already in y; and *)
(* `Send', which sends an arbitrarily chosen value in y and remove it from *)
(* y.  The definitions, leading up to the definition of the specification  *)
(* Spec, are straightforward.                                              *)
(*                                                                         *)
(* We consider x to be externally visible and y to be an internal          *)
(* variable.  The sender's Send action and the receiver's Rcv action,      *)
(* which change x, are therefore considered to be externally visible; the  *)
(* sender's Choose action, which changes only y, is considered to be an    *)
(* internal action.  In other words, we consider \EE y : Spec to be the    *)
(* "real" specification.                                                   *)
(***************************************************************************)
CONSTANT Data

NonData == CHOOSE d : d \notin Data

VARIABLES x, y
vars == <<x, y>>

TypeOK == /\ x \in Data \cup {NonData}
          /\ y \in SUBSET Data
          
Init == (x = NonData) /\ (y = {})

Choose == /\ \E d \in Data \ y : y' = y \cup {d}
          /\ x' = x
          
Send == /\ x = NonData 
        /\ x' \in y
        /\ y' = y \ {x'}
        
Rcv == /\ x \in Data
       /\ x' = NonData
       /\ y' = y
       
Next == Choose \/ Send \/ Rcv

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Sat Oct 22 00:40:17 PDT 2016 by lamport
\* Created Wed Sep 14 03:25:35 PDT 2016 by lamport
