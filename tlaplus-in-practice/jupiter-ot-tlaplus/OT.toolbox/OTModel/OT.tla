----------------------------- MODULE OT -----------------------------
EXTENDS Naturals

CONSTANTS 
    CH, 
    POS,
    PR,
    LOP,
    ROP

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
============================================================================