Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Transitive_Closure.
Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique coqutil.Byte.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Properties.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.MetricLogging.
Require Export bedrock2.Memory.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Classes.Morphisms.

Require Import Coq.Wellfounded.Union.
Require Import Relation_Operators.
Require Import Relation_Definitions.
Require Import Transitive_Closure.
Require Import Coq.Logic.ChoiceFacts.

Require Import equiv.EquivDefinitions.
Require Import equiv.EquivProof.

Require Import Coq.Lists.List.

Section WithEnv.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Context (e: env).

  (*Theorem 3.3 of the paper*)
  Lemma exec_det_equiv_nondet s k t m l mc fpost :
    excluded_middle ->
    FunctionalChoice_on (option sstate) (option sstate) ->
    ext_spec.ok ext_spec ->
    word.ok word ->
    map.ok mem ->
    (forall pick_sp,
        exec_nondet e s k t m l mc (fun k' t' m' l' mc' =>
                                      exists k'',
                                        k' = k'' ++ k /\
                                          (compat (fun k_ => consume_word (pick_sp (rev k_ ++ k))) (List.rev k'') ->
                                           fpost pick_sp k' t' m' l' mc')))
    <->
      (forall pick_sp,
          exec_det e pick_sp s k t m l mc (fpost pick_sp)).
  Proof.
    intros em choice ext_spec_ok word_ok mem_ok. split.
    - intros H pick_sp. apply step_to_exec; try assumption. revert pick_sp.
      pose proof det_equiv_nondet as P. cbv [possible_execution_det satisfies_det] in P.
      rewrite <- P by assumption. clear P. intros pick_sp. apply exec_to_step; try assumption.
      cbv [exec_nondet] in H. eapply pick_sp_irrel with (pick_sp1 := _). eapply H.
    - intros H pick_sp. eapply pick_sp_irrel with (pick_sp1 := _).
      apply step_to_exec; try assumption. revert pick_sp.
      pose proof det_equiv_nondet as P. cbv [possible_execution_nondet satisfies_nondet] in P.
    
      rewrite P by assumption. intros pick_sp. apply exec_to_step; try assumption.
      apply H.
  Qed.
End WithEnv.
