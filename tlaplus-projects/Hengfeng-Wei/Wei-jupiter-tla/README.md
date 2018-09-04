# tlaplus-jupiter project

## AJupiter.tla

### ToCheck
- \A a, b \in S
  - \A a \in S: \A b \in S \ {a}:
- Int, Nat
  - Definition Override
- Nop

### Problems
- AJupiter.dot vs. AJupiter_linveness.dot (syntax error in it)
- How many times: "Termination" is satisfied?

### TODO
- [x] Priority in model automatically generated 
- [ ] Uniqueness of Insertions (using cid + seq)
- [ ] Uniqueness of Messages (mid: uid + seq)
  - Set of messages vs. Bag of messages
- [x] History variable for AJupiter
  - [x] AJupiterH.tla
- [ ] AJupiter with fixed inputs for each replia
  - AJupiterFixedInput
  - simulation mode
  - simulation-guided testing (generating all possible interleavings due to communication)

## CJupiter.tla

### TODO


## General Problems

- [ ] Extract more "statistics" and generate pretty figures
  - resize windows
  - export raw data (cvs?)
- [ ] Refactoring and Testing
  - [ ] Run multiple models
  - [ ] Compare results/statistics with previous results/statistics
