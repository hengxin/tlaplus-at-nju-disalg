------------------------------ MODULE Peterson ------------------------------
EXTENDS Integers, TLAPS

Not(i) == IF i = 0 THEN 1 ELSE 0

(***************************************************************************
--algorithm Peterson{
    variables flag = [i \in {0, 1} |-> FALSE], turn = 0;
    process (proc \in {0, 1}) {
        a0: while(TRUE){
        a1:     flag[self] := TRUE;
        a2:     turn := Not(self);
       a3a:     if (flag[Not(self)]) {goto a3b} else {goto cs};
       a3b:     if (turn = Not(self)) {goto a3a} else {goto cs};
        cs:     skip;
        a4:     flag[self] :=FALSE;
            }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES flag, turn, pc

vars == << flag, turn, pc >>

ProcSet == ({0, 1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in ProcSet |-> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << flag, turn >>

a1(self) == /\ pc[self] = "a1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ turn' = turn

a2(self) == /\ pc[self] = "a2"
            /\ turn' = Not(self)
            /\ pc' = [pc EXCEPT ![self] = "a3a"]
            /\ flag' = flag

a3a(self) == /\ pc[self] = "a3a"
             /\ IF flag[Not(self)]
                   THEN /\ pc' = [pc EXCEPT ![self] = "a3b"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << flag, turn >>

a3b(self) == /\ pc[self] = "a3b"
             /\ IF turn = Not(self)
                   THEN /\ pc' = [pc EXCEPT ![self] = "a3a"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << flag, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED << flag, turn >>

a4(self) == /\ pc[self] = "a4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ turn' = turn

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3a(self) \/ a3b(self)
                 \/ cs(self) \/ a4(self)

Next == (\E self \in {0, 1}: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

MutualExclusion == (pc[0] # "cs") \/ (pc[1] # "cs")

TypeOK == /\ pc \in [{0, 1} -> {"a0", "a1", "a2", "a3a", "a3b", "cs", "a4"}]
          /\ turn \in {0, 1}
          /\ flag \in [{0, 1} -> BOOLEAN]
          
I == \A i \in {0, 1}:
        /\ pc[i] \in {"a2", "a3a", "a3b", "cs", "a4"} => flag[i]
        /\ pc[i] \in {"cs", "a4"} => /\ pc[Not(i)] \notin {"cs", "a4"}
                                     /\ pc[Not(i)] \in {"a3a", "a3b"} => turn = i
                                     
Inv == TypeOK /\ I











THEOREM Spec => []MutualExclusion
<1>1. Init => Inv
    BY Zenon, Isa DEFS Init, Inv, TypeOK, I, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
\*    BY DEFS Inv, Next, TypeOK, I, Not, proc, a0, a1, a2, a3a, a3b, cs, a4, vars
  <2>1. SUFFICES ASSUME Inv, Next
                 PROVE Inv'
    BY Zenon, Isa DEFS Inv, TypeOK, I, vars
  <2>2. TypeOK'
    BY Zenon, Isa, <2>1 
      DEFS Inv, TypeOK, Next, proc, a0, a1, a2, a3a, a3b, cs, a4, Not 
  <2>3. I'
    <3>1. SUFFICES ASSUME NEW j \in {0, 1}
                   PROVE  I!(j)'
      BY Zenon, Isa DEFS I
    <3>2. PICK i \in {0, 1}: proc(i)
      BY Zenon, Isa, <2>1 
        DEFS Next, I, TypeOK, Next, proc, a0, a1, a2, a3a, a3b, cs, a4, Not 
    <3>3. CASE i = j
      BY Zenon, Isa, <2>1, <3>2, <3>3
        DEFS Inv, I, TypeOK, proc, a0, a1, a2, a3a, a3b, cs, a4, Not 
    <3>4. CASE i # j
      BY Zenon, Isa, <2>1, <3>2, <3>4
        DEFS Inv, I, TypeOK, proc, a0, a1, a2, a3a, a3b, cs, a4, Not 
    <3>5. QED
      BY Zenon, Isa, <3>3, <3>4
  <2>4. QED
    BY Zenon, Isa, <2>2, <2>3 DEFS Inv
<1>3. Inv => MutualExclusion
    BY Zenon, Isa DEFS MutualExclusion, Inv, I, Not
<1>4. QED
    BY Zenon, Isa, <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================
\* Modification History
\* Last modified Tue Jan 15 12:40:02 GMT+08:00 2019 by pure_
\* Last modified Mon Jan 14 22:22:59 CST 2019 by stary
\* Created Fri Jan 11 10:38:09 CST 2019 by stary
