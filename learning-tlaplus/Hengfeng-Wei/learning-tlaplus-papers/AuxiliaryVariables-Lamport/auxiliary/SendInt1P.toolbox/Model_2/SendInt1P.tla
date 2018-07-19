----------------------------- MODULE SendInt1P -----------------------------
(***************************************************************************)
(* This module is part of the example from the paper "Auxiliary Variables  *)
(* in TLA+" that also includes module SendInt1 and SendInt2.  It adds a    *)
(* one-prediction prophecy variable p to specification Spec of SendInt1 to *)
(* obtain specification SpecP, and it defines a refinement mapping under   *)
(* which SpecP implements specification Spec of module SendInt2.           *)
(***************************************************************************)
EXTENDS SendInt1

(***************************************************************************)
(* Pi is the set of possible values of (predictions made by) p.            *)
(***************************************************************************)
Pi == Int

(***************************************************************************)
(* The operator PredSend is used in the definition of SendP below.  We     *)
(* define it before the declaration of the variable p to allow us more     *)
(* easily to check the theorem that follows it.  This theorem asserts      *)
(* condition (4.9) of "Auxiliary Variables in TLA+", which ensures that    *)
(* \EE p : SpecP (the specification obtained by hiding p in SpecP) is      *)
(* equivalent to Spec.  To check this theorem with TLC, temporarily end    *)
(* the module by adding few "=" characters after the theorem and create a  *)
(* model having Spec as the specification.                                 *)
(***************************************************************************)
PredSend(i) == x' = i
            
THEOREM Spec => [][Send => \E i \in Pi : PredSend(i)]_x
----------------------------------------------------------------------------
VARIABLE p
 
varsP == <<x, p>>

InitP ==  Init /\ (p \in Pi)

TypeOKP == TypeOK  /\ (p \in Pi)

SendP ==  Send /\ PredSend(p) /\ (p' \in Pi)

RcvP == Rcv /\ (p' = p) 

NextP == SendP \/ RcvP

SpecP == InitP /\ [][NextP]_varsP
-----------------------------------------------------------------------------
(***************************************************************************)
(* The theorem below asserts that SpecP implements SendInt2 under the      *)
(* refinement mapping defined by the INSTANCE statement.                   *)
(***************************************************************************)
SI2 == INSTANCE SendInt2 WITH z <- IF x = NotInt THEN p ELSE NotInt

THEOREM SpecP => SI2!Spec
=============================================================================
\* Modification History
\* Last modified Sat Oct 22 00:37:21 PDT 2016 by lamport
\* Created Tue Sep 06 02:21:32 PDT 2016 by lamport
