# tlaplus-jupiter project

## AJupiter.tla

### ToCheck
- \A a, b \in S
  - \A a \in S: \A b \in S \ {a}:
- Nop: definition override

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

### TypeOK
- cur[r]: always largest node

### Properties to Check
- [ ] All csses are (strongly) eventually the same

### FIXME
- [ ] Find an error involving 16 states
  - 3 clients + 2 chars
  - sctx error

### Improvement
- [ ] css: edge
  - [ ] using sequence instead of set?
- [ ] sctx: using sequence instead of set

### TODO
- [ ] Refactor CJupiter and AJupiter => Extract common "Jupiter" module
- [ ] Dynamic schedule graph
  - Only in simulation mode?
  - Using Animation Module?
- [ ] Dynamic CSS graph


## General Problems

- [ ] Extract more "statistics" and generate pretty figures
  - resize windows
  - export raw data (cvs?)
- [ ] Refactoring and Testing
  - [ ] Run multiple models
  - [ ] Compare results/statistics with previous results/statistics

## CSComm

### TODO
- [ ] cincoming[c], sincoming (for s) => incoming[r]
