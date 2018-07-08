# TLA+ AJupiter

## Model of AJupiter

## Specifications of AJupiter

## Model Checking AJupiter

### For Weak/Strong List Specification
#### Requirements of Model

- All inserted elements are distinct.
  - Using a single global source for issued operations.
  - Generate op sequence for each client
- Ins and Del should be legal. 
  - Excluded at Do(c) step.
  - Changed to legal operations at Do(c) step. [Now I use this method.]
    - Problem: the same priority value for one client
- Check wlspec at the terminated state.
