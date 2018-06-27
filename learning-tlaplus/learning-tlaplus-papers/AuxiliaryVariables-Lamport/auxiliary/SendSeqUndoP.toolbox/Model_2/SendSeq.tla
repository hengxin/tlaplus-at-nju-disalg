------------------------------ MODULE SendSeq ------------------------------
(***************************************************************************)
(* This module and modules SendSeqUndo and SendSeqUndoP form the SendSeq   *)
(* example from Section 4.4 of the paper "Auxiliary Variables in TLA+".    *)
(* It is a variant of the SendSet example in modules SendSet, SendSetUndo, *)
(* and SendSetUndoP.  The difference between the two examples is that the  *)
(* value of variable y in SendSet is a set of data values that may be sent *)
(* in any order.  In the current SendSeq example, the value of y is a      *)
(* sequence of data values that are to be sent in order.  The Undo(S)      *)
(* action of SendSetUndo that removes the set S of data values from the    *)
(* set y is replaced in SendSeqUndo by an Undo(i) action that removes      *)
(* element number i from the sequence y.                                   *)
(*                                                                         *)
(* If you understand module SendSet, you should have no problem            *)
(* understanding the current module.                                       *)
(***************************************************************************)
EXTENDS Sequences, Integers

CONSTANT Data

NonData == CHOOSE v : v \notin Data

VARIABLES x, y
vars == <<x, y>>

TypeOK == /\ x \in Data \cup {NonData}
          /\ y \in Seq(Data)
          
Init == (x = NonData) /\ (y = <<>>)

Choose == /\ \E d \in Data : y' = Append(y, d)
          /\ x' = x
          
Send == /\ x = NonData /\ y # << >>
        /\ x' = Head(y)
        /\ y' = Tail(y)
        
Rcv == /\ x \in Data
       /\ x' = NonData
       /\ y' = y
       
Next == Choose \/ Send \/ Rcv

Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Wed Oct 19 05:15:04 PDT 2016 by lamport
\* Created Thu Sep 15 02:12:27 PDT 2016 by lamport
