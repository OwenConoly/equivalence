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

  Lemma exec_det_equiv_nondet s k t m l mc fpost :
    excluded_middle ->
    FunctionalChoice_on (option sstate) (option sstate) ->
    ext_spec.ok ext_spec ->
    word.ok word ->
    map.ok mem ->
    (forall pick_sp,
        exec_nondet e pick_sp s k t m l mc (fun k' t' m' l' mc' =>
                                              exists k'',
                                                k' = k'' ++ k /\
                                                  (compat (fun k_ => consume_word (pick_sp (rev k_ ++ k))) (List.rev k'') ->
                                                   fpost pick_sp k' t' m' l' mc')))
    <->
      (forall pick_sp,
          exec_det e pick_sp s k t m l mc (fpost pick_sp)).
  Proof. apply EquivProof.exec_det_equiv_nondet. Qed.
End WithEnv.
