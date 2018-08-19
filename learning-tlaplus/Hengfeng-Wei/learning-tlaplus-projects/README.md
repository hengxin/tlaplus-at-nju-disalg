# Poker

# Model
- InitCard: (1 :> (2 :> 1 @@ 5 :> 1 @@ 9 :> 2 @@ 12 :> 2 @@ 13 :> 2) @@ 2 :> (1 :> 2 @@ 11 :> 2))

# TODO
- redefine '>'

# Problems
- Deal(p) used in Next?
- Java heap size
- NotType == CHOOSE t : t \notin Type
  - Type == {Single, Double}
  - Single == 0 
  - Double == 1
- How to specify the goal: to show that a player has a winning strategy (even against a smart adversary).


# Issues to TLA+
- TypeOK error: located to the line
- static check: v vs. v' (give a warning)
