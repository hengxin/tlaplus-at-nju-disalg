-------------------------- MODULE DieHard --------------------------


(***************************************************************************
--algorithm DieHard {
variables big = 0, small = 0;
{ while (TRUE)
{ either big := 5
 \* fill the big jug
or
 small := 3 \* fill the small jug
or
 big := 0
 \* empty the big jug
or
 small := 0 \* empty the small jug
or
 \* pour from small to big
with (poured = Min (big + small, 5) - big)
{ big
 := big + poured ;
small := small - poured }
or
 \* pour from big to small
with (poured = Min (big + small, 3) - small)
{ big
 := big - poured ;
small := small + poured }
}
}
}
***************************************************************************)

EXTENDS Integers

Min(m,n) == IF m < n THEN m ELSE n
 
\* BEGIN TRANSLATION
VARIABLES big, small

TypeOK == /\ big \in 0..5
          /\ small \in 0..3

vars == << big, small >>

Init == (* Global variables *)
        /\ big = 0
        /\ small = 0

Next == \/ /\ big' = 5
           /\ small' = small
        \/ /\ small' = 3
           /\ big' = big
        \/ /\ big' = 0
           /\ small' = small
        \/ /\ small' = 0
           /\ big' = big
        \/ /\ LET poured == Min (big + small, 5) - big IN
                /\ big' = big + poured
                /\ small' = small - poured
        \/ /\ LET poured == Min (big + small, 3) - small IN
                /\ big' = big - poured
                /\ small' = small + poured

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
 ===========================================================
