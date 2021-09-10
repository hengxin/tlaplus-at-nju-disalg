----------------------------- MODULE DieHarder -----------------------------
EXTENDS Integers

Min(m, n) == IF m < n THEN m ELSE n

CONSTANTS Goal, Jugs, Capacity

ASSUME /\ Goal \in Nat
       /\ Capacity \in [Jugs -> Nat \ {0}]
       
(***************************************************************************
--algorithm DieHarder{
    variable injug = [j \in Jugs |-> 0];
    {
        (*while(TRUE) {
            with(j \in Jugs){
                either {
                    injug[j] := Capacity[j]
                }
                or {
                    injug[j] := 0
                }
                or with(k \in Jugs \ {j}) {
                   with(poured = Min(injug[j] + injug[k], Capacity[k]) - injug[k]) {
                       injug[j] := injug[j] - poured ||
                       injug[k] := injug[k] + poured
                   } 
                }
                    
            }
        }*)
        while(TRUE){
            either with(j \in Jugs){ \* full jug j
                       injug[j] := Capacity[j]  
                   } 
            or     with(j \in Jugs){ \*empty jug j
                       injug[j] := 0
                   }
            or     with(j \in Jugs, k \in Jugs \ {j}){ \*pour from jug j to jug k
                       with(poured = Min(injug[j] + injug[k], Capacity[k]) - injug[k]) {
                           injug[j] := injug[j] - poured || injug[k] := injug[k] + poured
                   }
               }
        }
    }    
}


 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLE injug

vars == << injug >>

Init == (* Global variables *)
        /\ injug = [j \in Jugs |-> 0]

Next == \/ /\ \E j \in Jugs:
                injug' = [injug EXCEPT ![j] = Capacity[j]]
        \/ /\ \E j \in Jugs:
                injug' = [injug EXCEPT ![j] = 0]
        \/ /\ \E j \in Jugs:
                \E k \in Jugs \ {j}:
                  LET poured == Min(injug[j] + injug[k], Capacity[k]) - injug[k] IN
                    injug' = [injug EXCEPT ![j] = injug[j] - poured,
                                           ![k] = injug[k] + poured]

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Apr 09 15:28:19 GMT+08:00 2018 by pure_
\* Created Sun Mar 25 16:33:39 GMT+08:00 2018 by pure_
