--------------------------------- MODULE ot ---------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS POS

Intervals == { << a, b >> \in POS \X POS: a <= b }

\* IntervalPS == SUBSET Intervals

\* NonOverlappingIntervals == { ints \in SUBSET Intervals : \A i \in ints, j \in ints: (i[2] < j[1] \/ j[2] < i[1]) }

NonOverlappingIntervals == { ints \in SUBSET Intervals : \A i \in ints, j \in ints : (i[2] < j[1] \/ j[2] < i[1]) }
=============================================================================
\* Modification History
\* Last modified Sat Apr 28 23:14:03 CST 2018 by hengxin
\* Created Sat Apr 28 20:51:31 CST 2018 by hengxin
