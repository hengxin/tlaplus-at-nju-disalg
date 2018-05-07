--------------------------------- MODULE OT ---------------------------------
EXTENDS Integers,Sequences,Naturals,TLC
CONSTANTS LIST,CH,STR,PR,LEN,POS
Maxnum(set) == CHOOSE i \in set:\A j \in set:i>=j \* max int 

Intervals == {<<a,b>> \in POS \X POS: a+b<=Maxnum(POS)+1 }
NOIIntervals == {ints \in SUBSET Intervals : \A i,j \in ints: i[2]+i[1] <= j[1] \/ j[2]+j[1] <= i[1] \/ i=j} \{{}}

RECURSIVE SetTOSeq(_)
SetTOSeq(T) == IF T = {} THEN <<>>
                       ELSE LET t == CHOOSE x \in T : TRUE
                            IN   <<t>> \o SetTOSeq(T \ {t})
RECURSIVE Seqset(_)
Seqset(T) == IF T = {} THEN {}
                       ELSE LET t == CHOOSE x \in T : TRUE
                            IN   Seqset(T \ {t}) \union {SetTOSeq(t)} 
NOISEQ == Seqset(NOIIntervals)

\*RECURSIVE SetSize(_)
\*SetSize(T) == IF T = {} THEN 0
\*                       ELSE LET t == CHOOSE x \in T : TRUE
\*                            IN   1 + SetSize(T \ {t})
\*Minint(ints) == CHOOSE i \in ints:\A j \in ints:i[1]<=j[1] \* min int   
 
\*compare(a,b) == IF a[1]<b[1] THEN TRUE ELSE FALSE
                                                  

\*settoseq(set,list) == 
\*    IF set != "" THEN Append(list,Minint(set))
\*                ELSE list  
\*Durint(ints,pos) ==  CHOOSE i \in ints:i[1]<=pos /\ pos<=i[2] 

\*IF_Durint(ints,pos) == \E i \in ints : i[1]<pos /\ pos<i[2]
\*RECURSIVE SetSum(_)
\*SetSum(T) == IF T = {} THEN 0
\*                       ELSE LET t == CHOOSE x \in T : TRUE
\*                            IN  t[2] - t[1] + 1 + SetSum(T \ {t})

OP_1 == [type: {"del","ins","set"}, pos: POS, ch: CH, pr:PR] 
OP_2 == [type: {"del_r","ins_r"}, pos: POS, pr:PR, str:STR, len:LEN] 
OP_2_i == [type: {"ins_r"}, pos: POS, pr:PR, str:STR] 
OP_3 == [type:{"del_m"},ints:NOISEQ]

exm1 == [ints |-> <<<<1, 1>> , <<4,1>>>>, type |-> "del_m"]
exm2 == [ints |-> <<<<1, 1>> , <<3,3>>>>, type |-> "del_m"]
\*priority 2 > 1
\*lpop == del(1)  
\*rpop == del(LEN)
\*lpush == ins(1,ch)
\*rpush == ins(LEN+1,ch)

                          
NOP_ALL == [type: {"null"}, pos: {"null"}] 
NOP == CHOOSE v \in NOP_ALL: v \in NOP_ALL

\* the first kind of opreations
del_op(list,pos) == SubSeq(list, 1, pos-1) \o SubSeq(list, pos+1, Len(list))
ins_op(list,pos,ch) == SubSeq(list, 1, pos-1) \o ch \o SubSeq(list, pos, Len(list)) 
set_op(list,pos,ch) == SubSeq(list, 1, pos-1) \o ch \o SubSeq(list, pos+1, Len(list)) 
\* the second kind of operations
ins_ran_op(list,pos,str) == SubSeq(list, 1, pos-1) \o str \o SubSeq(list, pos, Len(list)) \*insert interval
del_ran_op(list,pos,len) == SubSeq(list, 1, pos-1) \o SubSeq(list, pos+len, Len(list)) \*delete interval
\* the third kind of operations ( how to express many intervals? )
RECURSIVE del_mulran_op(_,_,_)
del_mulran_op(list,ints,num) == 
    IF num = 0 THEN list 
    ELSE  del_mulran_op(SubSeq(list, 1, ints[num][1]-1) \o SubSeq(list, ints[num][2]+ints[num][1],Len(list)),ints,num-1) \*delete intervals
       
\* the fist kind of OT 
\*ins
Xform_ins_ins(lins, rins) == 
    IF lins.pos < rins.pos
    THEN lins
    ELSE IF lins.pos > rins.pos
        THEN [lins EXCEPT !.pos = @ + 1]
        ELSE IF lins.pr < rins.pr
                THEN [lins EXCEPT !.pos = @+1]
                ELSE lins

Xform_ins_del(ins, del) == 
    IF ins.pos <= del.pos
    THEN ins
    ELSE [ins EXCEPT !.pos = @-1] 
                     
Xform_ins_set (ins, set) == ins                    


\*del         
Xform_del_ins(del, ins) ==
    IF del.pos < ins.pos
    THEN del
    ELSE [del EXCEPT !.pos = @+1]
    
Xform_del_del(ldel, rdel) == 
    IF ldel.pos < rdel.pos                                                                                      
    THEN ldel
    ELSE IF ldel.pos > rdel.pos
         THEN  [ldel EXCEPT !.pos = @-1]
         ELSE NOP
         
Xform_del_set (del, set) == del 

\*set
Xform_set_set (lset,rset) ==
    IF lset.pr > rset.pr /\ lset.pos = rset.pos
    THEN NOP
    ELSE lset
    
Xform_set_ins (set,ins) ==
    IF set.pos >= ins.pos
    THEN  [set EXCEPT !.pos = @ +1]
    ELSE set
 
Xform_set_del (set,del) ==
    IF set.pos > del.pos
    THEN  [set EXCEPT !.pos = @-1]
    ELSE IF set.pos < del.pos
         THEN set
         ELSE NOP
         
\* the second kind of OT 
Xform_ins_ins_r(lins, rins) == 
    IF  lins.pos < rins.pos 
    THEN lins
    ELSE IF lins.pos > rins.pos
         THEN [lins EXCEPT !.pos = @ + Len(rins.str)]
         ELSE IF lins.pr > rins.pr
              THEN lins
              ELSE [lins EXCEPT !.pos = @ + Len(rins.str)]
              
Xform_ins_del_r(ins,del) ==
    CASE ins.pos <= del.pos -> ins
    [] ins.pos > del.pos /\ ins.pos < del.pos + del.len -> NOP
    [] ins.pos >= del.pos + del.len -> [ins EXCEPT !.pos = @ - del.len]
    
Xform_del_ins_r(del,ins) ==
    CASE ins.pos <= del.pos -> [del EXCEPT !.pos = @ + Len(ins.str)]
    [] ins.pos > del.pos /\ ins.pos < del.pos + del.len -> [del EXCEPT !.len = @ + Len(ins.str)]
    [] ins.pos >= del.pos + del.len -> del

Xform_del_del_r(ldel, rdel) == 
    CASE ldel.pos + ldel.len <= rdel.pos -> ldel
    [] ldel.pos < rdel.pos /\  ldel.pos + ldel.len > rdel.pos /\ ldel.pos + ldel.len <= rdel.pos + rdel.len -> [ldel EXCEPT !.len = rdel.pos - ldel.pos]
    [] ldel.pos < rdel.pos /\ ldel.pos + ldel.len > rdel.pos + rdel.len -> [ldel EXCEPT !.len = ldel.len - rdel.len]
    [] ldel.pos < rdel.pos /\ ldel.pos + ldel.len > rdel.pos + rdel.len -> [ldel EXCEPT !.len = ldel.len - rdel.len]
    [] ldel.pos >= rdel.pos /\ ldel.pos < rdel.pos +rdel.len /\ ldel.pos + ldel.len <= rdel.pos + rdel.len
       ->NOP
    [] ldel.pos >= rdel.pos /\ ldel.pos < rdel.pos +rdel.len /\ ldel.pos + ldel.len > rdel.pos + rdel.len
       ->[ldel EXCEPT !.pos=rdel.pos , !.len = ldel.pos + ldel.len - rdel.pos - rdel.len]
    [] ldel.pos >= rdel.pos + rdel.len -> [ldel EXCEPT !.pos = @ - rdel.len]
    
RECURSIVE dellen(_,_,_,_) 
dellen(del,pos,len,i) == IF i = 0 THEN len
                         ELSE IF del.ints[i][1]+del.ints[i][2] <= pos THEN dellen(del,pos,len+del.ints[i][2],i-1)
                         ELSE dellen(del,pos,len,i-1)
                   
Xform_insr_delm(ins,del) ==
    CASE ins.pos <= del.ints[1][1] ->ins
    [] \E i \in 1..Len(del.ints):del.ints[i][1] < ins.pos /\ ins.pos < del.ints[i][1] + del.ints[i][2] -> NOP
    [] \E i \in 1..Len(del.ints)-1:ins.pos >= del.ints[i][1] +  del.ints[i][2]/\ ins.pos <= del.ints[i+1][1] -> [ins EXCEPT !.pos = @ - dellen(del,@,0,Len(del.ints))]
    [] ins.pos >= del.ints[Len(del.ints)][1] + del.ints[Len(del.ints)][2] ->[ins EXCEPT !.pos = @ - dellen(del,@,0,Len(del.ints))]
    
    
    
RECURSIVE transdel1(_,_,_)
transdel1(del,i,len) == IF Len(del.ints) = i THEN [del EXCEPT !.ints[i][1] = @ +len]
                        ELSE transdel1([del EXCEPT !.ints[i][1]=@ + len],i+1,len)
                      
RECURSIVE transdel2(_,_,_,_)
transdel2(del,i,pos,len) == IF Len(del.ints) < i THEN del
                            ELSE IF del.ints[i][1] < pos /\ pos < del.ints[i][1] + del.ints[i][2] THEN transdel2([del EXCEPT !.ints[i][2]=@ + len],i+1,pos,len)
                            ELSE IF del.ints[i][1] > pos  THEN transdel2([del EXCEPT !.ints[i][1]=@ + len],i+1,pos,len)
                            ELSE IF Len(del.ints) = i THEN [del EXCEPT !.ints[i][1]=@ + len]
                            ELSE transdel2(del,i+1,pos,len)

                            
RECURSIVE transdel3(_,_,_,_)
transdel3(del,i,pos,len) == IF Len(del.ints) < i THEN del
                            ELSE IF pos <= del.ints[i][1] THEN transdel3([del EXCEPT !.ints[i][1]=@ + len],i+1,pos,len)
                            ELSE IF Len(del.ints) = i THEN [del EXCEPT !.ints[i][1]=@ + len]
                            ELSE transdel3(del,i+1,pos,len)
                        
                      
Xform_delm_insr(del,ins) ==
    CASE ins.pos <= del.ints[1][1] -> transdel1(del,1,Len(ins.str))
    [] \E i \in 1..Len(del.ints):del.ints[i][1] < ins.pos /\ ins.pos < del.ints[i][1] + del.ints[i][2] ->transdel2(del,1,ins.pos,Len(ins.str))
    [] \E i \in 1..Len(del.ints)-1:ins.pos >= del.ints[i][1] +  del.ints[i][2] /\ ins.pos <= del.ints[i+1][1] -> transdel3(del,1,ins.pos,Len(ins.str))
    [] ins.pos >= del.ints[Len(del.ints)][1] + del.ints[Len(del.ints)][2] ->del
RECURSIVE Dlen(_,_,_)
Dlen(ints,i,sum) == IF i=0 THEN sum
                   ELSE Dlen(ints,i-1,sum+ints[i][2])

RECURSIVE newpos(_,_,_)
newpos(pos,ints,i) ==
     IF  pos < ints[1][1] THEN pos
     ELSE IF i=Len(ints) /\ pos >= ints[i][1] + ints[i][2] THEN pos - Dlen(ints,i,0)
     ELSE IF pos >= ints[i][1] /\ pos < ints[i][1] + ints[i][2] THEN ints[i][1] - Dlen(ints,i-1,0)
     ELSE IF ints[i][1] + ints[i][2] <= pos /\ pos < ints[i+1][1] THEN pos - Dlen(ints,i,0)
     ELSE newpos(pos,ints,i+1)
     
RECURSIVE newlen(_,_,_,_,_)     
newlen(pos,len,ints,i,sum) == 
    IF i > Len(ints) THEN len - sum
    ELSE IF pos + len < ints[i][1] THEN newlen(pos,len,ints,i+1,sum)
    ELSE IF pos < ints[i][1] /\ ints[i][1] < pos + len /\ pos + len <= ints[i][1] + ints[i][2] THEN newlen(pos,len,ints,i+1,sum + pos + len -ints[i][1])
    ELSE IF pos < ints[i][1] /\ pos + len > ints[i][1] + ints[i][2] THEN newlen(pos,len,ints,i+1,sum + ints[i][2])
    ELSE IF ints[i][1] <= pos /\ pos < ints[i][1] + ints[i][2] /\ pos + len <= ints[i][1] + ints[i][2] THEN 0
    ELSE IF ints[i][1] <= pos /\ pos < ints[i][1] + ints[i][2] /\ pos + len > ints[i][1] + ints[i][2] THEN newlen(pos,len,ints,i+1,sum + ints[i][1] + ints[i][2] - pos)    
    ELSE newlen(pos,len,ints,i+1,sum)
    
transdel4(int,ints) == 
   <<newpos(int[1],ints,1),newlen(int[1],int[2],ints,1,0)   >>
   
RECURSIVE Xform_del_del_m(_,_,_)
Xform_del_del_m (ldel,rdel,i) == IF i > Len(ldel.ints) THEN ldel
                                 ELSE Xform_del_del_m ([ldel EXCEPT !.ints[i]= transdel4(@,rdel.ints)],rdel,i+1)
    
Xform(lop, rop) == \* the left operation is transformed against the right operation
    CASE  lop.type = "ins" /\ rop.type = "ins" -> Xform_ins_ins(lop, rop)
    []  lop.type = "ins" /\ rop.type = "del" -> Xform_ins_del(lop, rop)
    []  lop.type = "ins" /\ rop.type = "set" -> Xform_ins_set(lop, rop)   

    []  lop.type = "del" /\ rop.type = "ins" -> Xform_del_ins(lop, rop)
    []  lop.type = "del" /\ rop.type = "del" -> Xform_del_del(lop, rop) 
    []  lop.type = "del" /\ rop.type = "set" -> Xform_del_set(lop, rop) 
    
    []  lop.type = "set" /\ rop.type = "ins" -> Xform_set_ins(lop, rop)
    []  lop.type = "set" /\ rop.type = "del" -> Xform_set_del(lop, rop) 
    []  lop.type = "set" /\ rop.type = "set" -> Xform_set_set(lop, rop)
     
    []  lop.type = "ins_r" /\ rop.type = "ins_r" -> Xform_ins_ins_r(lop, rop)
    []  lop.type = "ins_r" /\ rop.type = "del_r" -> Xform_ins_del_r(lop, rop)
    []  lop.type = "del_r" /\ rop.type = "del_r" -> Xform_del_del_r(lop, rop)
    []  lop.type = "del_r" /\ rop.type = "ins_r" -> Xform_del_ins_r(lop, rop)
    
    []  lop.type = "ins_r" /\ rop.type = "del_m" -> Xform_insr_delm(lop, rop)    
    []  lop.type = "del_m" /\ rop.type = "ins_r" -> Xform_delm_insr(lop, rop)
        
    []  lop.type = "del_m" /\ rop.type = "del_m" -> Xform_del_del_m(lop, rop,1)
    
apply(list,op) ==     \* apply operation to a list
    CASE op.type = "del"  -> del_op(list,op.pos)
    [] op.type = "ins"  -> ins_op(list,op.pos,op.ch)
    [] op.type = "set" -> set_op(list,op.pos,op.ch)
    [] op.type = "ins_r" -> ins_ran_op(list,op.pos,op.str)
    [] op.type = "del_r" -> del_ran_op(list,op.pos,op.len)
    [] op.type = "del_m" -> del_mulran_op(list,op.ints,Len(op.ints)) 
    [] OTHER -> list

correctness_1 (list) == \* OT1 correctness
    \A op1,op2 \in OP_1:
         \/ op1.pr = op2.pr
         \/ apply(apply(list,op1),Xform(op2, op1)) = apply(apply(list,op2),Xform(op1, op2))  


correctness_2 (list) == \* OT1 correctness
    \A op1,op2 \in OP_2:
         \/ op1.pr = op2.pr
         \/ apply(apply(list,op1),Xform(op2, op1)) = apply(apply(list,op2),Xform(op1, op2)) 
         
correctness_3 (list) == \* OT1 correctness
    \A op1 \in OP_3, op2 \in OP_2_i:
         \/ apply(apply(list,op1),Xform(op2, op1)) = apply(apply(list,op2),Xform(op1, op2)) 
         
correctness_4 (list) == \* OT1 correctness
    \A op1,op2 \in OP_3:
         \/ apply(apply(list,op1),Xform(op2, op1)) = apply(apply(list,op2),Xform(op1, op2)) 
             
=============================================================================
\* Modification History
\* Last modified Sun May 06 18:41:03 CST 2018 by xhdn
\* Created Wed Apr 18 14:07:40 CST 2018 by xhdn
