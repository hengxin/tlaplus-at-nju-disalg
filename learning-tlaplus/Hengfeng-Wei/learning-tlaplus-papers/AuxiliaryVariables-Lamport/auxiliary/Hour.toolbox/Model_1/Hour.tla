-------------------------------- MODULE Hour --------------------------------
(***************************************************************************)
(* This module is part of the trivial example from Section 5 of the paper  *)
(* "Auxiliary Variables in TLA+".  The other modules in that example are   *)
(* HourMin and Stuttering.                                                 *)
(*                                                                         *)
(* The module begins by defining a trivial specification Spec of a 24-hour *)
(* clock that begins with h=0 and cycles through the integers mod 24.      *)
(***************************************************************************)
EXTENDS Integers
VARIABLE h

Init == h=0

Next == h' = (h + 1) % 24
      
Spec == Init /\ [][Next]_h
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now add a stuttering variable s that adds 59 stuttering steps before *)
(* each Next step, using the PreStutter operator of module Stuttering.     *)
(* The set Sigma of possible values s.val for the stuttering variable will *)
(* be 1..59, taking > as the "less-than" ordering on Sigma.  Thus, the     *)
(* minimal value bot of Sigma is 59, the initial value s.val is set to is  *)
(* 1, and the decrement operator maps a value i to i+1.  The following     *)
(* assumption and theorem are the correctness conditions for adding        *)
(* stuttering steps to Next.                                               *)
(***************************************************************************)

THEOREM Spec => [][Next => (1 \in 1..59)]_h
=======
vars == h
VARIABLE s 
INSTANCE Stuttering  
ASSUME StutterConstantCondition(1..59, 59, LAMBDA j : j+1)
InitS == Init /\ (s = top)

NextS == PreStutter(Next, TRUE, "Next", "", 59, 1, LAMBDA j : j+1) 

SpecS == InitS /\ [][NextS]_<<vars, s>>

HM == INSTANCE HourMin WITH m <- IF s = top THEN 0 ELSE s.val

THEOREM SpecS => HM!Spec
=============================================================================
\* Modification History
\* Last modified Thu Oct 20 05:35:29 PDT 2016 by lamport
\* Created Sun Oct 02 07:32:03 PDT 2016 by lamport
