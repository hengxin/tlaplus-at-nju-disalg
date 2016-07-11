----------------------------- MODULE HSClock -----------------------------
EXTENDS Integers
CONSTANT N
ASSUME (N \in Nat) /\ (N > 0)

a (+) b == (a + b) % 2
(***************************************************************************
--algorithm HSClock {
  variable ca = [ i \in 0 .. (N-1) |-> 0 ];
  
  process ( Proc0 = 0 )
    {  t: while ( TRUE )
            {  await ca[0] = ca[N-1];
               ca[0] := ca[0] (+) 1
            }
    }
    
  process ( Proc \in 1 .. (N-1) )
    {  t: while ( TRUE )
            {  await ca[self] # ca[self - 1];
               ca[self] := ca[self] (+) 1
            }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
\* Label t of process Proc0 at line 12 col 11 changed to t_
VARIABLE ca

vars == << ca >>

ProcSet == {0} \cup (1 .. (N-1))

Init == (* Global variables *)
        /\ ca = [ i \in 0 .. (N-1) |-> 0 ]

Proc0 == /\ ca[0] = ca[N-1]
         /\ ca' = [ca EXCEPT ![0] = ca[0] (+) 1]

Proc(self) == /\ ca[self] # ca[self - 1]
              /\ ca' = [ca EXCEPT ![self] = ca[self] (+) 1]

Next == Proc0
           \/ (\E self \in 1 .. (N-1): Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

cBar == IF \E i \in 1 .. (N-1) : ca[i] # ca[i-1]
           THEN CHOOSE i \in 1 .. (N-1) : ca[i] # ca[i-1]
           ELSE 0
           
CS == INSTANCE ClockSpec WITH c <- cBar
==========================================================================
