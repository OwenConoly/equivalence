Definitions and theorems about them are in equiv/Statements.v.
Proofs are in equiv/Proofs.v.
bedrock2 is included as a dependency only for some definitions of data structures and memory predicates (and also for definitions of syntax).
Other than this, the two files equiv/Statements.v and equiv/Proofs.v are self-contained.


List of contents:

* Theorem 3.3 of the paper: Lemma titled exec_det_equiv_nondet
* Theorem 4.3 of the paper: Lemma titled predictor_plus_oracle_equals_trace
* Corollary 4.4 of the paper: Theorem titled predictors_to_oracles
  Note that predictors_to_oracles is not directly the statement of Corollary 4.4.  Instead, it is the statement that the two postconditions appearing in Corollary 4.4 are equivalent (after you push the forall A into the RHS postcondition).
* Theorem C.3 of the paper: Theorem titled trace_trees_are_predictors
* Lemma D.1 of the paper: Lemma titled append_predictors
