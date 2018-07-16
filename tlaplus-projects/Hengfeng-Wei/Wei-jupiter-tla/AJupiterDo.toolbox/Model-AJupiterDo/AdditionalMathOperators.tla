---------------------- MODULE AdditionalMathOperators ----------------------
EXTENDS Naturals

PosInt == Nat \ {0}

Min(x, y) ==
    IF x <= y
    THEN x
    ELSE y
=============================================================================
\* Modification History
\* Last modified Fri Jul 06 15:20:57 CST 2018 by hengxin
\* Created Fri Jul 06 13:08:50 CST 2018 by hengxin