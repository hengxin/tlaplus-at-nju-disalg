--------------------------- MODULE MCAlternatingBit -------------------------
EXTENDS AlternatingBit

INSTANCE ABCorrectness 

CONSTANTS msgQLen, ackQLen

SeqConstraint == /\ Len(msgQ) \leq msgQLen
                 /\ Len(ackQ) \leq ackQLen

SentLeadsToRcvd == \A d \in Data : (sent = d) /\ (sBit # sAck) ~> (rcvd = d)
=============================================================================
