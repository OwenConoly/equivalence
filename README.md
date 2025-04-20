# What is this
This repository contains proofs of theorems from the paper "Smooth, Integrated Proofs of Cryptographic Constant Time for Nondeterministic Programs and Compilers".  (TODO: add doi or something)

Here is a list of the theorems in the paper and the corresponding proofs in this repository.

* Theorem 4.3: `Lemma exec_det_equiv_nondet`, file `equiv/EquivTheorem.v`
* Theorem 5.3: `Lemma predictor_plus_oracle_equals_trace`, file `equiv/OtherTheorems.v`
* Corollary 5.4: `Theorem predictors_to_oracles` and `Theorem predictors_to_oracles_as_in_paper`, file `equiv/OtherTheorems.v`, 
* Theorem 5.5: `Theorem predictor_from_nowhere` and `Theorem oracles_to_predictors_as_in_paper`, file `equiv/OtherTheorems.v`
* claim that "predictor constant time is equivalent to constant time": `Theorem pred_ct_same_as_ct`, file `equiv/OtherTheorems.v`
* Theorem C.3: `Theorem trace_trees_are_predictors`, file `equiv/OtherTheorems.v`
* Theorem C.6: `Lemma predictors_are_co_trace_trees` and `Lemma co_trace_trees_are_predictors`, file `equiv/OtherTheorems.v`
* Lemma D.1: `Lemma append_predictors`, file `equiv/OtherTheorems.v`

# Version of Coq that works:
The Coq Proof Assistant, version 8.20.0
compiled with OCaml 5.3.0
