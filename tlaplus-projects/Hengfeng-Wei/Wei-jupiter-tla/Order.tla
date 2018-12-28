------------------------------- MODULE Order -------------------------------
(*
Order related operators.

See https://github.com/jameshfisher/tlaplus/blob/master/examples/TransitiveClosure/TransitiveClosure.tla
*)
----------------------------------------------------------------------------
(*
Domain of relation R.
*)
Dom(R) == {a : <<a, b>> \in R}

(*
Range of relation R.
*)
Ran(R) == {b : <<a, b>> \in R}

(*
Support of relation R.
*)
Support(R) == Dom(R) \cup Ran(R)

(*
Inverse of relation R.
*)
Inverse(R) == {<<b, a>> : <<a, b>> \in R}

GT(R, a) == {b \in Ran(R): <<a, b>> \in R}

LT(R, b) == {a \in Dom(R): <<a, b>> \in R}

(*
Restriction of relation R to a set of elements S
*)
R | S == R \cap S \times S

(*
Is R a reflexive relation on set S?
*)
Reflexive(S, R) == \forall a \in S: <<a, a>> \in R
    
(*
Is R a transitive relation (on its support set)?
*)
Transitive(R) == 
    LET S == Support(R)     
    IN  \forall a, b, c \in S: 
            (<<a, b>> \in R /\ <<b, c>> \in R) => <<a, c>> \in R
    
(*
Composition of two relations R and T.
*)
R ** T == 
    LET SR == Support(R) 
        ST == Support(T) 
    IN  {<<r, t>> \in SR \X ST : 
            \E s \in SR \cap ST : (<<r, s>> \in R) /\ (<<s, t>> \in T)}

(*
Transitive closure of relation R.
*)
RECURSIVE TC(_)
TC(R) == 
    LET RR == R ** R 
    IN  IF RR \subseteq R THEN R ELSE TC(R \cup RR) 
=============================================================================
\* Modification History
\* Last modified Tue Sep 25 18:46:35 CST 2018 by hengxin
\* Created Tue Sep 18 19:16:04 CST 2018 by hengxin