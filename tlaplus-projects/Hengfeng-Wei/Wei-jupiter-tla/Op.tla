--------------------------------- MODULE Op ---------------------------------
(*********************************************************************)
(* Model checking basic operations on strings                        *)
(* (i.e., list of characters).                                       *)
(*********************************************************************)

CONSTANTS   
    Char,   \* set of characters allowed
    MaxPos  \* max position allowed

----------------------------------------------------------------------
(*********************************************************************)
(* The set of all operations.                                        *)
(*********************************************************************)
Rd == [type: {"Rd"}] \* a read specifies no arguments
Del == [type: {"Del"}, pos: 1 .. MaxPos] \* a deletion specifies a position, indexed from 1
Ins == [type: {"Ins"}, pos: 1 .. MaxPos, ch: Char, pr: PosInt] \* an insertion also specifies a character and a priority

Op == Ins \cup Del  \* now we don't consider Rd operations
-----------------------------------------------------------------------------
(*********************************************************************)
(* Some operations for test.                                         *)
(*********************************************************************)
Del1 == [type |-> "Del", pos |-> 1]
Del2 == [type |-> "Del", pos |-> 2]
Del3 == [type |-> "Del", pos |-> 3]
Del4 == [type |-> "Del", pos |-> 4]
Ins1 == [type |-> "Ins", pos |-> 1, ch |-> "a", pr |-> 1]
Ins2 == [type |-> "Ins", pos |-> 2, ch |-> "b", pr |-> 2]
Ins3 == [type |-> "Ins", pos |-> 3, ch |-> "c", pr |-> 3]
Ops == <<Ins2, Del3, Ins1, Del2, Ins3, Del1>>
=============================================================================
\* Modification History
\* Last modified Tue Aug 28 15:36:45 CST 2018 by hengxin
\* Created Sat Jun 23 20:56:53 CST 2018 by hengxin