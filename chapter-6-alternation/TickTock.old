--------------------------------- MODULE TickTock ----------------------------
EXTENDS Sequences 

(***************************************************************************
--algorithm TickTock {
  variable b = 0;
  process ( Tick = 0 )
    { t0: while ( TRUE )
            { await b = 0;
              b := 1
            }
    }
    
  process ( Tock = 1 )
    { t1: while ( TRUE )
            { await b = 1;
              b := 0
            }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLE b

vars == << b >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ b = 0

Tick == /\ b = 0
        /\ b' = 1

Tock == /\ b = 1
        /\ b' = 0

Next == Tick \/ Tock

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
============================================================================== 
