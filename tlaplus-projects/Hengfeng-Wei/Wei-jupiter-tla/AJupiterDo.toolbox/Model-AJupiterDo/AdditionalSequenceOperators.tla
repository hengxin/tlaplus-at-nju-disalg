-------------------- MODULE AdditionalSequenceOperators --------------------

(* Copyright: https://github.com/bringhurst/tlaplus/blob/master/org.lamport.tla.toolbox.uitest/farsite/AdditionalSequenceOperators.tla *)
(*`^\addcontentsline{toc}{section}{AdditionalSequenceOperators}^'*)

EXTENDS Naturals,Sequences,FiniteSets
(* 
    The TLA+ Sequences module defines the operators Head and Tail for
    retrieving the first element of a sequence and all-but-the-first elements
    of a sequence, respectively.
    This module provides four operators that slightly generalize the notions
    of Head and Tail:
        First returns the first element of a sequence, equivalently to Head.
        Last returns the last element of a sequence.
        AllButFirst returns all-but-the-first elements of a sequence,
            equivalently to Tail.
        AllButLast returns all-but-the-last elements of a sequence.
    This module also provides several additional operators on sequences:
    IsElementInSeq is a predicate that is true when the specified value is an element
    of the specified sequence.
    IsSequenceOfSetElements is a predicate that is true when the specified
    sequence contains all and only elements of the specified set.
    IsSortedSequenceOfSetElements is a predicate that is true when the
    IsSequenceOfSetElements is true and the sequence is also sorted in increasing order.
    DeleteElement produces a sequence by deleting an indicated element from another
    sequence.
 *)

Prepend(s,e)== <<e>>\o s

First(seq)==seq[1]

Last(seq)==seq[Len(seq)]

AllButFirst(seq)==[i \in 1..(Len(seq)-1)|->seq[(i+1)]]

AllButLast(seq)==[i \in 1..(Len(seq)-1)|->seq[i]]

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
SeqMaxLen(S, n) ==  UNION {[1..m -> S] : m \in 0..n}

(****************************************************************)
(* Map on a sequence.                                           *)
(*                                                              *)
(* Copyright: https://www.learntla.com/libraries/sequences/     *)
(****************************************************************)
SeqMap(Op(_), seq) == [x \in DOMAIN seq |-> Op(seq[x])]
=============================================================================
\* Modification History
\* Last modified Fri Jul 06 13:43:17 CST 2018 by hengxin
\* Created Tue Jul 03 15:21:02 CST 2018 by hengxin
