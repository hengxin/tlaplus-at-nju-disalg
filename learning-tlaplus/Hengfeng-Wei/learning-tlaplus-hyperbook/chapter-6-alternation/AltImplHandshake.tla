----------------------------- MODULE AltImplHandshake ----------------------------
EXTENDS Integers

a (+) b == (a + b) % 2

(***************************************************************************
--algorithm AltImplHandshake{
  variable p = 0, c = 0;
  
  process ( Producer = 0 )
    \* variable tp = 0;  \* for Model_AltImplHandshake
    variable tp;  \* for Model_AltImplHandshake_ModelValue
    {  pe: while ( TRUE )
             {      \* await p = c;
                    tp := c;
               pe1: if (p # tp) { goto pe };
               put: skip;
               px:  p := p (+) 1
             }
    }

  process ( Consumer = 1 )
    \* variable tc = 0;  \* for Model_AltImplHandshake
    variable tc;  \* for Model_AltImplHandshake_ModelValue
    {  ce: while ( TRUE )
             {      \* await p # c;
                    tc := p;
               ce1: if (c = tc) { goto ce };
               get: skip;
               cx:  c := c (+) 1
             }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES p, c, pc, tp, tc

vars == << p, c, pc, tp, tc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ p = 0
        /\ c = 0
        (* Process Producer *)
        /\ tp = defaultInitValue
        (* Process Consumer *)
        /\ tc = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "pe"
                                        [] self = 1 -> "ce"]

pe == /\ pc[0] = "pe"
      /\ tp' = c
      /\ pc' = [pc EXCEPT ![0] = "pe1"]
      /\ UNCHANGED << p, c, tc >>

pe1 == /\ pc[0] = "pe1"
       /\ IF p # tp
             THEN /\ pc' = [pc EXCEPT ![0] = "pe"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "put"]
       /\ UNCHANGED << p, c, tp, tc >>

put == /\ pc[0] = "put"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![0] = "px"]
       /\ UNCHANGED << p, c, tp, tc >>

px == /\ pc[0] = "px"
      /\ p' = p (+) 1
      /\ pc' = [pc EXCEPT ![0] = "pe"]
      /\ UNCHANGED << c, tp, tc >>

Producer == pe \/ pe1 \/ put \/ px

ce == /\ pc[1] = "ce"
      /\ tc' = p
      /\ pc' = [pc EXCEPT ![1] = "ce1"]
      /\ UNCHANGED << p, c, tp >>

ce1 == /\ pc[1] = "ce1"
       /\ IF c = tc
             THEN /\ pc' = [pc EXCEPT ![1] = "ce"]
             ELSE /\ pc' = [pc EXCEPT ![1] = "get"]
       /\ UNCHANGED << p, c, tp, tc >>

get == /\ pc[1] = "get"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![1] = "cx"]
       /\ UNCHANGED << p, c, tp, tc >>

cx == /\ pc[1] = "cx"
      /\ c' = c (+) 1
      /\ pc' = [pc EXCEPT ![1] = "ce"]
      /\ UNCHANGED << p, tp, tc >>

Consumer == ce \/ ce1 \/ get \/ cx

Next == Producer \/ Consumer

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

pcBar == [i \in {0,1} |-> CASE i = 0 -> IF pc[0] = "pe1" THEN "pe"
                                                         ELSE pc[0]
                            [] i = i -> IF pc[1] = "ce1" THEN "ce"
                                                         ELSE pc[1] ]
                                                         
A == INSTANCE AltSpec WITH b <- p (+) c, pc <- pcBar
==================================================================================
