-------------------------------- MODULE GCD --------------------------------
EXTENDS Integers
Divides(p, n) == \E q \in Int : n = q * p
DivisorsOf(n) == {p \in Int : Divides(p, n)}
SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j
GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
SetGCD(T) == SetMax({d \in Int : \A t \in T : Divides(d, t)})
=============================================================================
\* Modification History
\* Last modified Mon Mar 26 11:19:32 CST 2018 by zfwang
\* Created Sat Mar 17 21:15:55 CST 2018 by zfwang
