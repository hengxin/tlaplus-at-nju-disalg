--------------------------------- MODULE ot ---------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS POS

Intervals == { << a, b >> \in POS \X POS: a <= b }

NonOverlappingIntervals == { ints \in SUBSET Intervals : 
                                  \A i \in ints, j \in ints : 
                                        (i = j \/ i[2] < j[1] \/ j[2] < i[1]) }
=============================================================================
\* Modification History
\* Last modified Thu May 03 20:20:35 CST 2018 by hengxin
\* Created Sat Apr 28 20:51:31 CST 2018 by hengxin