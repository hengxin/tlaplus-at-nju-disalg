--------------------------------- MODULE OT ---------------------------------
(*
Specification of OT (Operational Transformation) functions.
*)
EXTENDS Op
-----------------------------------------------------------------------------
OTII(lins, rins) == \* lins is transformed against rins
    IF lins.pos < rins.pos
    THEN lins
    ELSE IF lins.pos > rins.pos
         THEN [lins EXCEPT !.pos = @ + 1]
         ELSE IF lins.ch = rins.ch
              THEN Nop
              ELSE IF lins.pr < rins.pr
                   THEN lins
                   ELSE [lins EXCEPT !.pos = @ + 1]

OTID(ins, del) == \* ins is transformed against del
    IF ins.pos <= del.pos
    THEN ins
    ELSE [ins EXCEPT !.pos = @ - 1]

OTDI(del, ins) == \* del is transformed against ins
    IF del.pos < ins.pos
    THEN del
    ELSE [del EXCEPT !.pos = @ + 1]

OTDD(ldel, rdel) == \* ldel is transformed against rdel
    IF ldel.pos < rdel.pos
    THEN ldel
    ELSE IF ldel.pos > rdel.pos
         THEN [ldel EXCEPT !.pos = @ - 1]
         ELSE Nop

OT(lop, rop) == \* lop is transformed against rop
    CASE lop = Nop \/ rop = Nop -> lop
       []  lop.type = "Ins" /\ rop.type = "Ins" -> OTII(lop, rop)
       []  lop.type = "Ins" /\ rop.type = "Del" -> OTID(lop, rop)
       []  lop.type = "Del" /\ rop.type = "Ins" -> OTDI(lop, rop)
       []  lop.type = "Del" /\ rop.type = "Del" -> OTDD(lop, rop)
=============================================================================
\* Modification History
\* Last modified Sun Jan 13 10:41:55 CST 2019 by hengxin
\* Created Sun Jun 24 15:57:48 CST 2018 by hengxin