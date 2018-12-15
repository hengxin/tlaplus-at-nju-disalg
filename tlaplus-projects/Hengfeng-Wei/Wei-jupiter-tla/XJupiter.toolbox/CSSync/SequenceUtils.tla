-------------------- MODULE SequenceUtils --------------------
(* 
Copyright: https://github.com/bringhurst/tlaplus/blob/master/org.lamport.tla.toolbox.uitest/farsite/AdditionalSequenceOperators.tla
*)

EXTENDS FiniteSets, Sequences, SetUtils, FunctionUtils
LOCAL INSTANCE Naturals

(* 
IsSequenceOfSetElements is a predicate that is true when the specified
sequence contains all and only elements of the specified set.

IsSortedSequenceOfSetElements is a predicate that is true when the

IsSequenceOfSetElements is true and the sequence is also sorted in increasing order.
*)

Prepend(s,e) == <<e>> \o s

First(seq) == seq[1]

Last(seq) == seq[Len(seq)]

AllButFirst(seq) == [i \in 1..(Len(seq)-1) |-> seq[(i+1)]]

AllButLast(seq) == [i \in 1..(Len(seq)-1) |-> seq[i]]

DoesSeqPrefixSeq(seq1,seq2)==
  /\ Len(seq1)\leq Len(seq2)
  /\ (\A i \in 1..Len(seq1):seq1[i]=seq2[i])

DoesSeqProperlyPrefixSeq(seq1,seq2)==
  /\ Len(seq1)<Len(seq2)
  /\ (\A i \in 1..Len(seq1):seq1[i]=seq2[i])

IsElementInSeq(el,seq)==\E i \in DOMAIN seq:seq[i]=el

IsSequenceOfSetElements(seq,set)==
  /\ Len(seq)=Cardinality(set)
  /\ (\A el \in set:IsElementInSeq(el,seq))

IsSortedSequenceOfSetElements(seq,set)==
  /\ IsSequenceOfSetElements(seq,set)
  /\ (\A i \in DOMAIN seq,j \in DOMAIN seq:i<j=>seq[i]<seq[j])

DeleteElement(seq,index)==
  [i \in 1..(Len(seq)-1)|->IF i<index THEN seq[i]ELSE seq[(i+1)]]
  
(*
Retain only the elements in R in their original order in seq.
*)
RECURSIVE Retain(_,_)
Retain(seq, R) ==
    IF seq = <<>>
    THEN <<>>
    ELSE LET h == Head(seq)
          IN IF h \in R
             THEN <<h>> \o Retain(Tail(seq), R)
             ELSE Retain(Tail(seq), R)
(****************************************************************)
(* It requires that index >= 1.                                 *)
(*                                                              *)
(* If index > Len(seq) + 1, then it appends the element to seq. *)
(*                                                              *)
(* (ADDED by hengxin; July 04, 2018)                            *)
(****************************************************************)
InsertElement(seq, elem, index) ==
  [i \in 1 .. (Len(seq) + 1) |-> IF i < index
                                 THEN IF i = (Len(seq) + 1)
                                      THEN elem
                                      ELSE seq[i]
                                 ELSE IF i = index
                                      THEN elem
                                      ELSE seq[(i-1)]] \* i > index
  
IsSorted2Partition(n,seq1,seq2)==
  /\ seq1 \in Seq(1..n)
  /\ seq2 \in Seq(1..n)
  /\ n=Len(seq1)+Len(seq2)
  /\ (\A i \in DOMAIN seq1,j \in DOMAIN seq1:i<j=>seq1[i]<seq1[j])
  /\ (\A i \in DOMAIN seq2,j \in DOMAIN seq2:i<j=>seq2[i]<seq2[j])
  /\ (\A i \in DOMAIN seq1,j \in DOMAIN seq2:seq1[i]#seq2[j])

IsSequenceInterleaving(seq,subSeq1,subSeq2,indSeq1,indSeq2)==
  /\ indSeq1 \in Seq(Nat)
  /\ indSeq2 \in Seq(Nat)
  /\ IsSorted2Partition(Len(seq),indSeq1,indSeq2)
  /\ Len(indSeq1)=Len(subSeq1)
  /\ Len(indSeq2)=Len(subSeq2)
  /\ (\A i \in DOMAIN indSeq1:seq[(indSeq1[i])]=subSeq1[i])
  /\ (\A i \in DOMAIN indSeq2:seq[(indSeq2[i])]=subSeq2[i])

(****************************************************************)
(* Sequences up to length n, including the empty sequence <<>>. *)
(*                                                              *)
(* Copyright: https://www.learntla.com/libraries/sequences/     *)
(****************************************************************)
SeqMaxLen(S, n) ==  UNION {[1 .. m -> S] : m \in 0 .. n}

(****************************************************************)
(* Map on a sequence.                                           *)
(*                                                              *)
(* Copyright: https://www.learntla.com/libraries/sequences/     *)
(****************************************************************)
SeqMap(Op(_), seq) == [x \in DOMAIN seq |-> Op(seq[x])]

PermsWithin(S) ==  {s \in UNION {[1 .. m -> S] : m \in 0 .. Cardinality(S)} : Cardinality(Range(s)) = Cardinality(DOMAIN s)}

(****************************************************************)
(* All possible permutations generated based on sequence T.     *)
(*                                                              *)
(* Copyright: https://learntla.com/tla/functions/               *)
(****************************************************************)
PermutationKey(n) == {key \in [1..n -> 1..n] : Range(key) = 1..n}
PermutationsOf(T) == { [x \in 1..Len(T) |-> T[P[x]]] : P \in PermutationKey(Len(T))}
(****************************************************************)
(* Get the index of the first occurrence of elem in seq.        *)
(*                                                              *)
(* Precondition: elem \in SeqImage(seq).                        *)
(*                                                              *)
(* ADDED by hengxin; Aug. 12, 2018                              *)
(****************************************************************)
RECURSIVE FirstIndexOfElement(_,_)
FirstIndexOfElement(seq, elem) ==
    IF Head(seq) = elem
    THEN 1
    ELSE 1 + FirstIndexOfElement(Tail(seq), elem)

(*
Get the index of the first occurence of elem in seq.
It returns 0 if elem does not occur in seq.
*)
RECURSIVE FirstIndexOfElementSafe(_,_)
FirstIndexOfElementSafe(seq, elem) == 
    LET RECURSIVE FirstIndexOfElementSafeHelper(_,_,_)
        FirstIndexOfElementSafeHelper(seqh, elemh, fail) ==
            IF seqh = <<>>
            THEN 0-fail
            ELSE IF Head(seqh) = elemh
                 THEN 1
                 ELSE 1 + FirstIndexOfElementSafeHelper(Tail(seqh), elemh, fail + 1)
     IN FirstIndexOfElementSafeHelper(seq, elem, 0)
(****************************************************************)
(* Check if two sequences are compatible.                       *)
(*                                                              *)
(* Precondition: No duplication in each individual sequence.                        *)
(*                                                              *)
(* Two sequences are compatible if and only if for any two common elements *)
(* in both sequences, the relative order of them in the two     *)
(* sequences are the same.                                      *)
(*                                                              *)
(* ADDED by hengxin; Aug. 12, 2018                              *)
(****************************************************************)
Compatible(seq1, seq2) ==
    \/ seq1 = seq2
    \/ LET commonElements == Range(seq1) \cap Range(seq2)
       IN \A e1, e2 \in commonElements:
            \/ e1 = e2
            \/ FirstIndexOfElement(seq1, e1) < FirstIndexOfElement(seq1, e2) 
               <=> FirstIndexOfElement(seq2, e1) < FirstIndexOfElement(seq2, e2)
            
(****************************************************************)
(* The length of the longest common subsequence of two sequences seq1 and seq2.                       *)
(*                                                              *)
(* ADDED by hengxin; Aug. 12, 2018                              *)
(****************************************************************)
RECURSIVE LCS(_,_)
LCS(seq1, seq2) ==
    IF seq1 = <<>> \/ seq2 = <<>>
    THEN 0
    ELSE IF Last(seq1) = Last(seq2)
         THEN 1 + LCS(AllButLast(seq1), AllButLast(seq2))
         ELSE MaxOfSet({LCS(AllButLast(seq1), seq2), LCS(seq1, AllButLast(seq2))})
         
LCSCompatible(seq1, seq2) == 
    Compatible(seq1, seq2) <=> LCS(seq1, seq2) = Cardinality(Range(seq1) \cap Range(seq2))
    
LCSCompatibleTest(S) ==
    \A seq1, seq2 \in PermsWithin(S): LCSCompatible(seq1, seq2)
=============================================================================
\* Modification History
\* Last modified Tue Dec 04 19:42:23 CST 2018 by hengxin
\* Created Tue Jul 03 15:21:02 CST 2018 by hengxin