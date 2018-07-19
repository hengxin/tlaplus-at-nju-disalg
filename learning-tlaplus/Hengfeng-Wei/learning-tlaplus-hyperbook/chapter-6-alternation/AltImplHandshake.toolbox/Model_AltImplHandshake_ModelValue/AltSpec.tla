----------------------------- MODULE AltSpec -----------------------------
(***************************************************************************
--algorithm AltSpec{
  variable b = 0;
  
  process ( Producer = 0 )
    { pe: while ( TRUE )
            {       await b = 0;
               put: skip;
               px:  b := 1
            }
    } 

  process ( Consumer = 1 )
    { ce: while ( TRUE )
            {       await b = 1;
               get: skip;
               cx:  b := 0
            }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES b, pc

vars == << b, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ b = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "pe"
                                        [] self = 1 -> "ce"]

pe == /\ pc[0] = "pe"
      /\ b = 0
      /\ pc' = [pc EXCEPT ![0] = "put"]
      /\ b' = b

put == /\ pc[0] = "put"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![0] = "px"]
       /\ b' = b

px == /\ pc[0] = "px"
      /\ b' = 1
      /\ pc' = [pc EXCEPT ![0] = "pe"]

Producer == pe \/ put \/ px

ce == /\ pc[1] = "ce"
      /\ b = 1
      /\ pc' = [pc EXCEPT ![1] = "get"]
      /\ b' = b

get == /\ pc[1] = "get"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![1] = "cx"]
       /\ b' = b

cx == /\ pc[1] = "cx"
      /\ b' = 0
      /\ pc' = [pc EXCEPT ![1] = "ce"]

Consumer == ce \/ get \/ cx

Next == Producer \/ Consumer

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
==========================================================================
