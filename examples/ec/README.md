# Elliptic curve operations

`Makefile` - script to run the proof-checker

### `proofs/`
* `Parameters.ec` - parameters and their relations
* `AlmostYUL.ec` - parameterized version of the YUL code

### `proofs/montgomery_arith/`
* `redc.ec` - functional implementation and the respective correctness derivation for REDC algorithm.
* `opt_redc.ec` - proof of correctness of abstract imperative implementation of REDC (`AlmostYul._REDC`).
* `montgomert_arith.ec` - proofs of correctness for:
  - `into_m` - conversion into Montgomery form (MF)
  - `outof_m` - conversion out of MF
  - `add_m` - addition
  - `sub_m` - subtraction
  - `mul_m` - multiplication
  - `inv_m` - inversion
  - `div_m` - division

### `proofs/ecAdd/` 
* `ecAdd_spec.ec` - functional specification of curve related functions
* `ecAdd_props.ec` - correctness and safety of `ecAdd`
* `ecAdd_safety_cases.ec` - derivation of safety for "out-of-range" and "out-of-curve" cases
* `ecAdd_correctness_cases.ec` - correctness derivation for ecAdd (P + inf, inf + P, P - P, P + P, P + Q)

### `proofs/auxiliary_lemmas/`
* `ExtraFacts.ec` - auxiliary lemmas.

### `sources/`
* `ModularInverter.sol` - contract for gas-consumption testing for two versions of `binaryExtendedEuclideanAlgorithm`.
  - `test2` - original version of modular inversion
  - `test1` - new version of modular inversion (~5k gas cheaper than the original version on Remix)
* `mod_inv.py` - script for runtime testing
