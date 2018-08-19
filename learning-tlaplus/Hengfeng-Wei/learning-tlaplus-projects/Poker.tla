------------------------------- MODULE Poker -------------------------------

EXTENDS Naturals, TLC

\* TODO: redefine '>'

NonType == 0
Single == 1
Double == 2

CONSTANTS
    MaxFace,
    MaxDuplicate,
    NumberOfPlayers,
    InitCard    \* InitCard[p]: Initial cards at the hand of player p \in Player

Face == 1 .. MaxFace
Hand == UNION {[f -> 0 .. MaxDuplicate] : f \in SUBSET Face}

Player == 1 .. NumberOfPlayers
NextPlayer(p) == 
    IF p < NumberOfPlayers
    THEN p + 1
    ELSE 1

Type == {NonType, Single, Double}

ASSUME
    /\ NumberOfPlayers \in Nat \ {0}
    /\ InitCard \in [Player -> Hand]
    
VARIABLES
   card,
   type,
   turn,
   max,
   skipno 
   
vars == <<card, type, turn, max, skipno>>

TypeOK ==
    /\ card \in [Player -> Hand]
    /\ type \in Type
    /\ turn \in Player
    /\ max \in Face \cup {0}
    /\ skipno \in 0 .. (NumberOfPlayers - 1)
    
Init == 
    /\ card = InitCard
    /\ type = NonType
    /\ turn \in Player
    /\ max = 0
    /\ skipno = NumberOfPlayers - 1

IsDealer(p) == 
    /\ turn = p
    /\ skipno = NumberOfPlayers - 1
    
IsNotDealer(p) ==
    /\ turn = p
    /\ skipno # NumberOfPlayers - 1

DealType(p, t) ==
    /\ IsDealer(p)
    /\ \E f \in (DOMAIN card[p]): card[p][f] >= t
    /\ max' \in {f \in (DOMAIN card[p]): card[p][f] >= t}
    /\ card' = [card EXCEPT ![p][max'] = @ - t]
    /\ type' = t
    /\ turn' = NextPlayer(p)
    /\ PrintT(turn')
    /\ skipno' = 0

Deal(p) ==  \* TODO: Is this correct when used in Next?
    \/ DealType(p, Single)
    \/ DealType(p, Double)
    
CallType(p, t) ==
    /\ IsNotDealer(p)
    /\ \E f \in (DOMAIN card[p]): 
        /\ card[p][f] >= t
        /\ f > max
    /\ max' \in {f \in (DOMAIN card[p]): card[p][f] >= t /\ f > max}
    /\ card' = [card EXCEPT ![p][max'] = @ - t]
    /\ turn' = NextPlayer(p)
    /\ UNCHANGED <<type, skipno>>
    
Call(p) == CallType(p, type)

Pass(p) ==
    /\ IsNotDealer(p)
    /\ turn' = NextPlayer(p)
    /\ skipno' = skipno + 1 
    /\ UNCHANGED <<card, type, max>>

Next == \E p \in Player: 
            \/ DealType(p, Single) 
            \/ DealType(p, Double)
            \/ Call(p)
            \/ Pass(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Win ==
    \E p \in Player:
        /\ \A f \in (DOMAIN card[p]): card[p][f] = 0
        /\ \A q \in Player:
            q # p => \E f \in (DOMAIN card[q]) : card[q][f] > 0
=============================================================================
\* Modification History
\* Last modified Sun Aug 19 15:45:07 CST 2018 by hengxin
\* Created Sat Aug 18 14:38:31 CST 2018 by hengxin