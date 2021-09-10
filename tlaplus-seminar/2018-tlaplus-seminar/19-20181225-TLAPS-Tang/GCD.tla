-------------------------------- MODULE GCD --------------------------------
EXTENDS Integers

(***************************************************************************)
(* For integers p and n, equals TRUE iff p divides n.                      *)
(***************************************************************************)
Divides(p, n) == \E q \in Int : n = q * p

(***************************************************************************)
(* Calculate all divisors of n                                             *)
(***************************************************************************)
DivisorsOf(n) == {p \in Int : Divides(p, n)}

(***************************************************************************)
(* Choose the max element of a set 'S'                                     *)
(***************************************************************************)
SetMax(S) == 
    CHOOSE i \in S : \A j \in S : i >= j

(***************************************************************************)
(* Greatest common divisor of m and n                                      *)
(***************************************************************************)
GCD(m, n) == 
    SetMax(DivisorsOf(m) \cap DivisorsOf(n))

THEOREM GCD1 == \A m \in Nat \ {0} : GCD(m, m) = m
  <1> SUFFICES ASSUME NEW m \in Nat \ {0}
               PROVE  GCD(m, m) = m
    OBVIOUS
    <1>1. Divides(m, m)
    BY DEF Divides
    <1>2. \A i \in Nat : Divides(i, m) => (i <= m)
    BY DEF Divides
  <1> QED
    BY <1>1, <1>2 DEF GCD, SetMax , DivisorsOf , Divides
               
THEOREM GCD2 == \A m, n \in Nat \ {0} : GCD(m, n) = GCD(n, m)
        BY DEF GCD, SetMax , DivisorsOf , Divides
THEOREM GCD3 == \A m, n \in Nat \ {0} : (n > m) => (GCD(m, n) = GCD(m, n-m))
  <1> SUFFICES ASSUME NEW m \in Nat \ {0}, NEW n \in Nat \ {0},
                      n > m
               PROVE  GCD(m, n) = GCD(m, n-m)
    OBVIOUS
  <1> \A i \in Int : Divides(i, m) /\ Divides(i, n) <=> Divides(i, m) /\ Divides(i, n - m)
    BY DEF Divides
  <1> QED
    BY DEF GCD, SetMax , DivisorsOf , Divides
        

=============================================================================
\* Modification History
\* Last modified Thu Dec 13 01:43:08 CST 2018 by tangruize
\* Created Wed Feb 28 08:19:46 CST 2018 by tangruize
