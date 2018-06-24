----------------------------- MODULE OT -----------------------------

EXTENDS Naturals, Sequences

CONSTANTS 
    CH, 
    POS,
    PR,

OP == [type: {"ins", "del"}, pos: POS, ch: CH, pr: PR]
NOP == CHOOSE v: v \notin OP

XformII(lins, rins) == \* the left insertion transformed against the right insertion
    IF lins.pos < rins.pos
    THEN lins
    ELSE IF lins.pos > rins.pos
        THEN [lins EXCEPT !.pos = @ + 1]
        ELSE IF lins.ch = rins.ch
            THEN NOP
            ELSE IF lins.pr > rins.pr
                THEN [lins EXCEPT !.pos = @+1]
                ELSE lins

XformID(ins, del) == \* the left insertion transformed against the right deletion
    IF ins.pos < del.pos
    THEN ins
    ELSE [ins EXCEPT !.pos = @-1]
                
XformDI(del, ins) == \* the first deletion transformed against the right insertion
    IF del.pos < ins.pos
    THEN del
    ELSE [del EXCEPT !.pos = @+1]
    
XformDD(ldel, rdel) == \* the first deletion transformed against the right deletion
    IF ldel.pos < rdel.pos
    THEN ldel
    ELSE IF ldel.pos > rdel.pos
        THEN [ldel EXCEPT !.pos = @-1]
        ELSE NOP

Xform(lop, rop) == \* the left operation is transformed against the right operation
    CASE lop.type = "ins" /\ rop.type = "ins" -> XformII(lop, rop)
    []  lop.type = "ins" /\ rop.type = "del" -> XformID(lop, rop)
    []  lop.type = "del" /\ rop.type = "ins" -> XformDI(lop, rop)
    []  lop.type = "del" /\ rop.type = "del" -> XformDD(lop, rop)
    
XformOpOps(op, ops) == \* the left operation is transformed against the right operation sequence
    LET X[j \in 1 .. Len(ops) + 1] ==
        IF j = 1
        THEN <<op>>
        ELSE Append(X[j-1], Xform(X[j-1][j-1], ops[j-1]))
    IN X[Len(ops) + 1]

XformOpsOp(ops, op) == \* the left operation sequence is transformed against the right single operation    
    LET T[i \in 0 .. Len(ops)] ==
        IF i = 0 
        THEN <<>>
        ELSE LET X == XformOpOps(op, ops)
             IN Append(T[i-1], Xform(ops[i], X[i]))
    IN T[Len(ops)]
============================================================================