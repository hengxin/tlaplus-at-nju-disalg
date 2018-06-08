------------------------------ MODULE DieHard ------------------------------
EXTENDS Integers

VARIABLES small, big   

TypeOK == /\ small \in 0..3 
          /\ big   \in 0..5

Init == /\ big   = 0 
        /\ small = 0

FillSmall == /\ small' = 3 
             /\ big'   = big

FillBig == /\ big'   = 5 
           /\ small' = small

EmptySmall == /\ small' = 0 
              /\ big'   = big

EmptyBig == /\ big'   = 0 
            /\ small' = small

(* using IF-THEN-ELSE *)
(*
SmallToBig == IF big + small =< 5
               THEN /\ big'   = big + small
                    /\ small' = 0
               ELSE /\ big'   = 5
                    /\ small' = small - (5 - big)

BigToSmall == IF big + small =< 3
               THEN /\ big'   = 0 
                    /\ small' = big + small
               ELSE /\ big'   = small - (3 - big)
                    /\ small' = 3
*)

(* using CNF *)
(*
SmallToBig == \/ /\ big + small =< 5
                 /\ big' = big + small
                 /\ small' = 0
              \/ /\ big + small > 5
                 /\ big' = 5
                 /\ small' = big + small - 5

BigToSmall == \/ /\ big + small =< 3
                 /\ small' = big + small
                 /\ big' = 0
              \/ /\ big + small > 3
                 /\ small' = 3
                 /\ big' = big + small - 3
*)

(* using LET/IN construct *)
Min(m, n) == IF m < n THEN m ELSE n

SmallToBig ==
    LET poured == Min(big + small, 5) - big
    IN  /\ big'   = big + poured
        /\ small' = small - poured

BigToSmall ==
    LET poured == Min(big + small, 3) - small
    IN  /\ big'   = big - poured
        /\ small' = small + poured

Next == \/ FillSmall 
        \/ FillBig    
        \/ EmptySmall 
        \/ EmptyBig    
        \/ SmallToBig    
        \/ BigToSmall
=============================================================================
\* Modification History
\* Last modified Thu Jan 25 11:40:42 CST 2018 by tangruize
\* Created Tue Jan 23 10:25:34 CST 2018 by tangruize
