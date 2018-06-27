------------------------------ MODULE SendInt1 ------------------------------
(***************************************************************************)
(* This is a specification of the same system described by module          *)
(* SendInt2, except without the variable z.  Each value to be sent is      *)
(* nondeterministically chosen by the Send action that sends it.           *)
(***************************************************************************)
EXTENDS Integers

NotInt == CHOOSE n : n \notin Int

VARIABLE x

TypeOK == x \in Int \cup {NotInt}

Init == x = NotInt

Send == /\ x = NotInt
        /\ x' \in Int

Rcv == /\ x \in Int
       /\ x' = NotInt

Next == Send \/ Rcv

Spec == Init /\ [][Next]_x
=============================================================================
\* Modification History
\* Last modified Wed Oct 19 02:28:14 PDT 2016 by lamport
\* Created Tue Sep 06 02:11:16 PDT 2016 by lamport
