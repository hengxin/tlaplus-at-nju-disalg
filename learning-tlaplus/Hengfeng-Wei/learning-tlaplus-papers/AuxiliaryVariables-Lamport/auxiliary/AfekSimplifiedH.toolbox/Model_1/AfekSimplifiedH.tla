---------------------------- MODULE AfekSimplifiedH ----------------------------
(***************************************************************************)
(* This module adds a history variable h to the algorithm in module        *)
(* AfekSimplified and shows that the resulting specification SpecH         *)
(* implements specification SafeSpec of module NewLinearSnapshot under a   *)
(* suitable refinement mapping.  This shows that specification Spec of     *)
(* module AfekSimplified implies \EE mem, rstate, wstate : SafeSpec.       *)
(*                                                                         *)
(* The history variable h is modified by the BeginRd, EndRd, and DoWr      *)
(* actions exactly the way the corresponding actions of NewLinearSnapshot  *)
(* change rstate, so the refinement mapping can instantiate rstate with h. *)
(* The instantiations of the other internal variables of NewLinearSnapshot *)
(* are straightforward.                                                    *)
(***************************************************************************)
EXTENDS AfekSimplified, Sequences

VARIABLE h
varsH == <<vars, h>>

TypeOKH == TypeOK /\ (h \in [Readers -> Seq(MemVals)])

InitH == Init /\ (h = [i \in Readers |-> << >>])

(***************************************************************************)
(* We define memBar to be the value of the variable mem of                 *)
(* NewLinearSnapshot represented by imem.  It is used both to instantiate  *)
(* the variable mem and in the definitions of the value of h' in some of   *)
(* the actions.                                                            *)
(***************************************************************************)
memBar == [i \in Writers |-> imem[i][1]]

BeginWrH(i, cmd) == BeginWr(i, cmd) /\ (h' = h)

DoWrH(i) == /\ DoWr(i) 
            /\ h' = [j \in Readers |-> 
                            IF h[j] = << >>
                              THEN << >>
                              ELSE Append(h[j], memBar')]

EndWrH(i) == EndWr(i) /\ (h' = h)

BeginRdH(i) == /\ BeginRd(i) 
               /\ h' = [h EXCEPT ![i] = <<memBar>>]

Rd1H(i) == Rd1(i) /\ (h' = h)

Rd2H(i) == Rd2(i) /\ (h' = h)

TryEndRdH(i) == /\ TryEndRd(i) 
                /\ h' = IF rdVal1[i] = rdVal2[i]
                          THEN [h EXCEPT ![i] = << >>]
                          ELSE h

NextH == 
  \/ \E i \in Readers : BeginRdH(i) \/ Rd1H(i) \/ Rd2H(i) \/ TryEndRdH(i)
  \/ \E i \in Writers : \/ \E cmd \in RegVals : BeginWrH(i, cmd)
                        \/ DoWrH(i) \/ EndWrH(i)  
                        
SpecH == InitH /\ [][NextH]_varsH                        
-----------------------------------------------------------------------------
(***************************************************************************)
(* We instantiate wstate with the following expression wstateBar.          *)
(***************************************************************************)
wstateBar == [i \in Writers |-> 
               IF (interface[i] = NotRegVal) \/ (wrNum[i] = imem[i][2])
                 THEN NotRegVal
                 ELSE interface[i]]

(***************************************************************************)
(* Here is the INSTANCE statement and theorem asserting that SpecH         *)
(* implements SafeSpec of module NewLinearSnapshot under the refinement    *)
(* mapping.  This theorem implies that the algorithm implements            *)
(*                                                                         *)
(*    \EE mem, rstate, wstate : Spec                                       *)
(*                                                                         *)
(* where Spec is the specification in NewLinearSnapshot.                   *)
(***************************************************************************)                
NLS == INSTANCE NewLinearSnapshot
          WITH mem <- memBar, rstate <- h, wstate <- wstateBar
               
THEOREM SpecH => NLS!SafeSpec
=============================================================================
\* Modification History
\* Last modified Sat Oct 22 02:03:17 PDT 2016 by lamport
\* Created Wed Oct 05 09:45:14 PDT 2016 by lamport
