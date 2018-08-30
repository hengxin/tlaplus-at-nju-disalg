# tlaplus-jupiter project

## ToCheck
- \A a, b \in S
  - \A a \in S: \A b \in S \ {a}:
- Int, Nat
  - Definition Override
- Nop

## Problems
- AJupiter.dot vs. AJupiter_linveness.dot (syntax error in it)
- How many times: "Termination" is satisfied?

## TODO
- [] Extract more "statistics" and generate pretty figures
  - resize windows
  - export raw data (cvs?)
- [x] Priority in model automatically generated 
- [ ] Uniqueness of Insertions (using cid + seq)
- [ ] Uniqueness of Messages (mid: uid + seq)
  - Set of messages vs. Bag of messages
- [ ] History variable for AJupiter
  - [ ] AJupiter-WLSpec.tla
- [ ] AJupiter with fixed inputs for each replia
  - AJupiterFixedInput
  - simulation mode
  - simulation-guided testing (generating all possible interleavings due to communication)
