Require Import Coq.Lists.List.
Require Import coqutil.Tactics.fwd.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.ChoiceFacts.
Require Import equiv.EquivProof. (*just for a tactic or two*)
Require Import equiv.EquivDefinitions.

Section ShortTheorems.
  Import Leakage.
  Context {L B : Type} (B_inhabited : B).
  Notation predicts := (@predicts L B).
  Notation compat := (@compat L B).
  Notation event := (@event L B).
  Notation qevent := (@qevent L).
  
  Lemma predicts'_iff_predicts pred k : predicts' pred k <-> predicts pred k.
  Proof.
    split.
    - revert pred.
      induction k as [|e k']; [|destruct e as [l|b]]; intros pred H; unfold predicts' in H; fwd.
      + constructor. assumption.
      + constructor.
        -- eapply Hp0. trace_alignment.
        -- eapply IHk'. cbv [predicts']. split; [|split].
           ++ intros. subst. eapply Hp0. trace_alignment.
           ++ intros. subst. eapply Hp1. trace_alignment.
           ++ assumption.
      + constructor.
        -- eapply Hp1. trace_alignment.
        -- eapply IHk'. cbv [predicts']. split; [|split].
           ++ intros. subst. eapply Hp0. trace_alignment.
           ++ intros. subst. eapply Hp1. trace_alignment.
           ++ assumption.
    - intros H. induction H.
      + split; [|split].
        -- intros. destruct k1; simpl in H0; congruence.
        -- intros. destruct k1; simpl in H0; congruence.
        -- assumption.
      + destruct IHpredicts as [H1 [H2 H3]]. split; [|split].
        -- intros. destruct k1; inversion H4; subst; simpl in *; try congruence.
           eapply H1. trace_alignment.
        -- intros. destruct k1; inversion H4; subst; simpl in *; try congruence.
           eapply H2. trace_alignment.
        -- assumption.
  Qed.

  Lemma compat'_iff_compat o k : compat' o k <-> compat o k.
  Proof.
    split.
    - intros H. revert o H. induction k; intros o H.
      + constructor.
      + destruct a.
        -- constructor. apply IHk. cbv [compat']. intros. subst. eapply H. trace_alignment.
        -- constructor.
           ++ eapply H. trace_alignment.
           ++ apply IHk. cbv [compat']. intros. subst. eapply H. trace_alignment.
    - intros H. cbv [compat']. induction H; intros.
      + destruct k1; simpl in H; congruence.
      + destruct k1; simpl in H1; try congruence. inversion H1. subst.
        eapply IHcompat. trace_alignment.
      + destruct k1; simpl in H0; try congruence. inversion H0. subst.
        eapply IHcompat. trace_alignment.
  Qed.

  (*as in section C.1 of the paper*)
  Inductive trace_tree : Type :=
  | tree_leaf
  | tree_leak (l : L) (rest : trace_tree)
  | tree_branch (rest : B -> trace_tree).

  (*Definition C.1 of the paper*)
  Inductive path : trace_tree -> list event -> Prop :=
  | nil_path : path tree_leaf nil
  | leak_path x k tree : path tree k -> path (tree_leak x tree) (leak x :: k)
  | branch_path k f x : path (f x) k -> path (tree_branch f) (branch x :: k).

  Fixpoint predictor_of_trace_tree (tree : trace_tree) : (list event -> qevent) :=
    fun k =>
      match tree, k with
      | tree_leaf, nil => qend
      | tree_leak l tree', nil => qleak l
      | tree_branch tree', nil => qbranch
      | tree_leak l1 tree', leak l2 :: k' => predictor_of_trace_tree tree' k'
      | tree_branch tree', branch b :: k' => predictor_of_trace_tree (tree' b) k'
      | _, _ => (*input is garbage, return whatever*) qend
      end.

  (*Theorem C.3 of the paper*)
  Theorem trace_trees_are_predictors :
    forall tree, exists pred, forall k,
      path tree k <-> predicts' pred k.
  Proof.
    intros. exists (predictor_of_trace_tree tree). intros. rewrite predicts'_iff_predicts.
    split; intros H.
    - induction H.
      + constructor. reflexivity.
      + constructor; [reflexivity|]. assumption.
      + constructor; [reflexivity|]. assumption.
    - revert k H. induction tree; intros k H'.
      + simpl in H'. inversion H'; simpl in *; subst.
        -- constructor.
        -- destruct e; simpl in H; congruence.
      + destruct k as [|e k'].
        { simpl in H'. inversion H'; subst. congruence. }
        destruct e.
        -- inversion H'. subst. simpl in H2. inversion H2. subst. constructor.
           apply IHtree. simpl in H3. apply H3.
        -- inversion H'. subst. simpl in H2. inversion H2.
      + destruct k as [|e k'].
        { simpl in H'. inversion H'; subst. congruence. }
        destruct e.
        -- inversion H'. subst. simpl in H3. inversion H3.
        -- inversion H'. subst. simpl in H3. inversion H3. subst. constructor.
           apply H. simpl in H4. apply H4.
  Qed.

  Fixpoint trace_of_predictor_and_oracle pred o fuel : option (list event) :=
    match fuel with
    | O => None
    | S fuel' =>
        match pred nil with
        | qend => Some nil
        | qleak l => option_map (cons (leak l)) (trace_of_predictor_and_oracle
                                                  (fun k_ => pred (leak l :: k_))
                                                  (fun k_ => o (leak l :: k_))
                                                  fuel')
                               
        | qbranch => option_map (cons (branch (o nil))) (trace_of_predictor_and_oracle
                                                          (fun k_ => pred (branch (o nil) :: k_))
                                                          (fun k_ => o (branch (o nil) :: k_))
                                                          fuel')
                               
        end
    end.

  (*Theorem 4.3 of the paper*)
  Lemma predictor_plus_oracle_equals_trace :
    excluded_middle ->
    FunctionalChoice_on ((list event -> B) * (list event -> qevent)) (option (list event)) ->
    exists trace,
    forall o pred k,
      compat o k ->
      (predicts pred k <-> Some k = trace (o, pred)).
  Proof.
    intros em choice. cbv [FunctionalChoice_on] in choice.
    specialize (choice (fun o_pred tr => let '(o, pred) := o_pred in forall k, compat o k -> predicts pred k <-> Some k = tr)).
    destruct choice as [trace choice].
    2: { exists trace. intros. specialize (choice (o, pred) k H). apply choice. }
    intros [o pred]. destruct (em (exists fuel, trace_of_predictor_and_oracle pred o fuel <> None)) as [H | H].
    - destruct H as [fuel H]. exists (match trace_of_predictor_and_oracle pred o fuel with
                                 | Some k => Some k
                                 | None => Some nil
                                 end).
      intros. destruct (trace_of_predictor_and_oracle pred o fuel) eqn:E; try congruence.
      clear H. revert l k pred o H0 E. induction fuel.
      + intros. simpl in E. congruence.
      + intros. simpl in E. split.
        -- intros H. destruct k as [|e k'].
           ++ inversion H. subst. rewrite H1 in E. inversion E. subst. reflexivity.
           ++ inversion H. subst. rewrite H4 in E. destruct e; simpl in E.
              --- destruct (trace_of_predictor_and_oracle _ _ _) eqn:E'; simpl in E; try congruence.
                  inversion E. subst. f_equal. inversion H0. subst. f_equal.
                  enough (Some k' = Some l0) by congruence. eapply IHfuel; eassumption.
              --- destruct (trace_of_predictor_and_oracle _ _ _) eqn:E'; simpl in E; try congruence.
                  inversion E. subst. inversion H0. subst. f_equal. f_equal.
                  enough (Some k' = Some l0) by congruence. eapply IHfuel; eassumption.
        -- intros H. inversion H. subst. clear H. destruct l as [|e l].
           ++ constructor. destruct (pred nil).
              --- destruct (trace_of_predictor_and_oracle _ _ _) eqn:E'; simpl in E; congruence.
              --- destruct (trace_of_predictor_and_oracle _ _ _) eqn:E'; simpl in E; congruence.
              --- reflexivity.
           ++ destruct (pred nil) eqn:E''.
              --- destruct (trace_of_predictor_and_oracle _ _ _) eqn:E'; simpl in E; try congruence.
                  inversion E. subst. inversion H0. subst. constructor.
                  +++ assumption.
                  +++ eapply IHfuel; try eassumption. reflexivity.
              --- destruct (trace_of_predictor_and_oracle _ _ _) eqn:E'; simpl in E; try congruence.
                  inversion E. subst. inversion H0. subst. constructor.
                  +++ assumption.
                  +++ eapply IHfuel; try eassumption. reflexivity.
              --- inversion E.
    - exists None. intros. split; intros H1; try congruence. exfalso. apply H. clear H.
      revert o pred H0 H1. induction k as [|e k'].
      + intros. exists (S O). simpl. inversion H1. rewrite H. congruence.
      + intros. destruct e.
        -- inversion H0. inversion H1. subst. specialize IHk' with (1 := H3) (2 := H9).
           destruct IHk' as [fuel IHk']. exists (S fuel). simpl. rewrite H8. simpl.
           destruct (trace_of_predictor_and_oracle _ _ _); try congruence. simpl.
           congruence.
        -- inversion H0. inversion H1. subst. specialize IHk' with (1 := H5) (2 := H10).
           destruct IHk' as [fuel IHk']. exists (S fuel). simpl. rewrite H9. simpl.
           destruct (trace_of_predictor_and_oracle _ _ _); try congruence. simpl. congruence.
  Qed.

  Fixpoint oracle_of_trace (k k_ : list event) : B :=
    match k, k_ with
    | branch b :: k', nil => b
    | _ :: k', _ :: k_' => oracle_of_trace k' k_'
    | _, _ => B_inhabited
    end.

  Lemma oracle_of_trace_works k :
    compat (oracle_of_trace k) k.
  Proof.
   induction k.
    - constructor.
    - destruct a; constructor; assumption || reflexivity.
  Qed.
  
  Lemma compat_exists :
    forall k, exists o, compat o k.
  Proof.
    intros k. exists (oracle_of_trace k). induction k.
    - constructor.
    - destruct a; constructor; assumption || reflexivity.
  Qed.

  (*Corollary 4.4 of the paper*)
  Theorem predictors_to_oracles {T T' : Type} :
    excluded_middle ->
    FunctionalChoice_on ((list event -> B) * (list event -> qevent)) (option (list event)) ->
    forall pred (g : T -> T'), exists f, forall k t,
      predicts (pred (g t)) k <-> (forall o, (compat o k -> Some k = f o (g t))).
  Proof.
    intros. specialize predictor_plus_oracle_equals_trace with (1 := H) (2 := H0).
    clear H H0. intros [trace H]. exists (fun o gt => trace (o, pred gt)).
    intros. split. 1: intros; apply H; assumption. intros.
    specialize (compat_exists k). intros [o Ho]. specialize (H0 o Ho). rewrite H; eassumption.
  Qed.

  Fixpoint p' (p1 : list event -> qevent) (p2 : list event -> list event -> qevent) (k : list event) :=
    match (p1 nil) with
    | qend => p2 nil k
    | _ => match k with
          | nil => (p1 nil)
          | x :: k' => p' (fun kk => p1 (x :: kk)) (fun kk => p2 (x :: kk)) k'
          end
    end.

  Fixpoint p  (p1 : list event -> qevent) (p2 : list event -> list event -> qevent) (k : list event) :=
    match k with
    | nil => match (p1 nil) with
            | qend => p2 nil k
            | _ => (p1 nil)
            end
    | x :: k' => match (p1 nil) with
               | qend => p2 nil k
               | _ => p (fun kk => p1 (x :: kk)) (fun kk => p2 (x :: kk)) k'
               end
    end.

  (*Lemma D.1 of the paper*)
  Lemma append_predictors p1 p2 : exists p,
    forall k1 k2, predicts p1 k1 -> predicts (p2 k1) k2 -> predicts p (k1 ++ k2).
  Proof.
    exists (p p1 p2). intros k1. revert p1 p2. induction k1; intros.
    - simpl. inversion H. subst. destruct k2; simpl.
      + inversion H0. subst. constructor. simpl. rewrite H1. assumption.
      + inversion H0. subst. constructor.
        -- simpl. rewrite H1. assumption.
        -- simpl. rewrite H1. assumption.
    - simpl. inversion H. subst. clear H.
      constructor.
      -- simpl. rewrite H4. destruct a; reflexivity.
      -- simpl. rewrite H4. destruct a.
         ++ simpl. apply IHk1. 1: assumption. assumption.
         ++ simpl. apply IHk1. 1: assumption. assumption.
  Qed.
  (*forall A k, prefix k f(A) -> forall B, compat B k -> prefix k f(B)*)

  Definition prefix {A: Type} (k1 k : list A) :=
    exists k2, k = k1 ++ k2.

  Print predicts.
  Fixpoint get_next (part whole : list event) : qevent :=
    match part, whole with
    | nil, leak x :: _ => qleak x
    | nil, branch _ :: _ => qbranch
    | nil, nil => qend
    | _ :: part', _ :: whole' => get_next part' whole'
    | _ :: _, nil => qend (*garbage*)
    end.
  
  Definition predictor_of_fun_alt (f : (list event -> B) -> list event) (k : list event) : qevent :=
    let full_trace := f (oracle_of_trace k) in
    get_next k full_trace.

  Lemma both_prefixes {A : Type} (l1 l2 : list A) :
    prefix l1 l2 ->
    prefix l2 l1 ->
    l1 = l2.
  Proof.
    intros [l2' H1] [l1' H2].
    replace l1 with (l1 ++ nil) in H2 by apply app_nil_r.
    rewrite H1 in H2. rewrite <- app_assoc in H2.
    apply app_inv_head in H2. destruct l2'; inversion H2.
    rewrite H1. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma prefix_refl {A : Type} (l : list A) :
    prefix l l.
  Proof. exists nil. symmetry. apply app_nil_r. Qed.
  
  Lemma full_thing_special_case f :
    (forall A k, prefix k (f A) -> forall B, compat B k -> prefix k (f B)) ->
    forall A B, compat B (f A) -> f B = f A.
  Proof.
    intros f_reasonable. intros o1 o2 Hcompat.
    epose proof (f_reasonable o1 (f o1) _ o2 _) as left.
    Unshelve. all: cycle 1.
    { apply prefix_refl. }
    { assumption. }
    destruct left as [nill left]. destruct nill.
    { rewrite app_nil_r in left. assumption. }
    epose proof (f_reasonable o2 (f o1 ++ e :: nil) _) as H'. Unshelve. all: cycle 1.
    { exists nill. rewrite <- app_assoc. simpl. assumption. }
    (*this is not true; suppose the program could 'look ahead' into the future to decide
      whether to take a branch.*)
  Abort.

  Import List.ListNotations.

  Definition fun_reasonable' (f : (list event -> B) -> list event) A B :=
    (forall k b1,
        prefix (k ++ [branch b1]) (f A) ->
        prefix k (f B) ->
        prefix (k ++ [branch (B k)]) (f B)) /\
      (forall k x,
          prefix (k ++ [leak x]) (f A) ->
          prefix k (f B) ->
          prefix (k ++ [leak x]) (f B)) /\
      (prefix (f A) (f B) ->
       f A = f B).

  Definition fun_reasonable possible f := forall A B, possible A -> possible B -> fun_reasonable' f A B.

  Lemma reasonableness_preserved possible f :
    fun_reasonable possible f ->
    fun_reasonable possible (fun o => match f o with
                          | _ :: l => l
                          | nil => nil
                          end).
  Proof. Abort. (*just not true*)

  Lemma reasonableness_preserved' f g b o1 o2 :
    let o1' := (fun k_ => match k_ with
                                                           | nil => b
                                                           | _ :: k_' => o1 k_'
                       end) in
    let o2' := (fun k_ => match k_ with
                            | nil => b
                            | _ :: k_' => o2 k_'
                            end) in
    fun_reasonable' f  o1' o2' ->
    (prefix ([g (o1' [])])(*first elt should only depend on A []*) (f o1')) ->
    (prefix ([g (o2' [])])(*first elt should only depend on A []*) (f o2')) ->
    fun_reasonable' (fun o0 : list event -> B =>
       match
         f (fun k_ : list event => match k_ with
                                   | [] => b
                                   | _ :: k_' => o0 k_'
                                   end)
       with
       | [] => []
       | _ :: k'_ => k'_
       end)
      o1 o2.
  Proof.
    intros o1' o2' H. split; [|split].
    - intros. destruct H as (H&_&_).
      specialize (H (g b :: k) b1).
      destruct H1 as (l1&H1). destruct H2 as (l2&H2).
      destruct (f _).
      { destruct H0. inversion H0. }
      destruct H0. inversion H0. subst. clear H0.
      destruct (f _).
      { discriminate H1. }
      inversion H1. subst. clear H1.
      destruct H3. subst.
      epose proof (H _ _) as H. Unshelve. all: cycle 1.
      { eexists. repeat rewrite <- app_assoc. simpl. reflexivity. }
      { eexists. repeat rewrite <- app_assoc. simpl. reflexivity. }
      destruct H. simpl in H. inversion H. clear H. rewrite <- app_assoc in H1.
      apply app_inv_head in H1. subst. eexists. rewrite <- app_assoc. reflexivity.
    - intros. destruct H as (_&H&_).
      specialize (H (g b :: k)).
      destruct H1 as (l1&H1). destruct H2 as (l2&H2).
      destruct (f _).
      { destruct H0. inversion H0. }
      destruct H3. inversion H3. subst. clear H3.
      destruct (f _).
      { discriminate H1. }
      subst. inversion H1. subst. clear H1.
      destruct H0. inversion H0. subst. clear H0.
      epose proof (H x _ _) as H. Unshelve. all: cycle 1.
      { eexists. repeat rewrite <- app_assoc. simpl. reflexivity. }
      { eexists. repeat rewrite <- app_assoc. simpl. reflexivity. }
      destruct H. simpl in H. inversion H. clear H. rewrite <- app_assoc in H1.
      apply app_inv_head in H1. subst. eexists. rewrite <- app_assoc. reflexivity.
    - intros. subst.
      destruct H0 as (?&H0'). inversion H0'. clear H0'. subst.
      destruct H1 as (?&H1'). inversion H1'. clear H1'. subst. subst o1' o2'.
      rewrite H1, H3. rewrite H1, H3 in H2. destruct H as (_&_&H). destruct H2. subst.
      rewrite H1, H3 in H. specialize (H ltac:(exists x1; reflexivity)).
      inversion H. repeat rewrite <- H2. reflexivity.
  Qed.

  Lemma lists_eq_iff {A : Type} (l1 l2 : list A) :
    l1 = l2 <-> (prefix l1 l2 -> l1 = l2) /\ (prefix l2 l1 -> l2 = l1)
              /\ (forall x1 x2 l, prefix (l ++ [x1]) l1 ->
                            prefix (l ++ [x2]) l2 ->
                            x1 = x2).
  Proof.
    revert l1 l2. split.
    - intros ?; subst. split; [auto|split; [auto|] ]. intros ? ? ? (l1'&H1) (l2'&H2).
      subst. repeat rewrite <- app_assoc in H2.
      apply app_inv_head in H2. inversion H2. reflexivity.
    - intros (H1&H2&H3). revert l2 H1 H2 H3. induction l1; intros l2 H1 H2 H3.
      { specialize (H1 ltac:(eexists; reflexivity)). subst. reflexivity. }
      destruct l2.
      { specialize (H2 ltac:(eexists; reflexivity)). discriminate H2. }
      pose proof (H3 a a0 nil ltac:(simpl; exists l1; reflexivity) ltac:(simpl; exists l2; reflexivity)).
      subst. f_equal. apply IHl1.
      + intros H.
        enough (H' : a0 :: l1 = a0 :: l2) by (inversion H'; subst; reflexivity).
        apply H1. destruct H as (l&H). exists l. rewrite H. reflexivity.
      + intros H.
        enough (H' : a0 :: l2 = a0 :: l1) by (inversion H'; subst; reflexivity).
        apply H2. destruct H as (l&H). exists l. rewrite H. reflexivity.
      + clear H1 H2. intros. specialize (H3 x1 x2 (a0 :: l)). apply H3.
        -- destruct H. rewrite H. eexists. reflexivity.
        -- destruct H0. rewrite H0. eexists. reflexivity.
  Qed.
     
  Lemma reasonable_ext f g1 g2 :
    fun_reasonable' f g1 g2 ->
    fun_reasonable' f g2 g1 ->
    fun_reasonable' f g1 g1 ->
    (forall k b1, prefix (k ++ [branch b1]) (f g1) -> g2 k = g1 k) ->
    f g1 = f g2.
  Proof. 
    intros f_reasonable1 f_reasonable2 f_reasonable3. intros Hsame. apply lists_eq_iff.
    split; [|split].
    - intros H. destruct f_reasonable1 as (_&_&f_end1).
      apply f_end1. assumption.
    - intros H. destruct f_reasonable2 as (_&_&f_end2).
      apply f_end2. assumption.
    - intros. destruct x1.
      + destruct f_reasonable1 as (_&f_leak1&_). specialize f_leak1 with (1 := H).
        destruct H0 as (?&H0). rewrite <- app_assoc in H0.
        destruct f_reasonable2 as (_&f_leak2&_).
        epose proof (f_leak1 _) as f_leak1. Unshelve. all: cycle 1.
        { eexists. eassumption. }
        destruct H as (?&H). destruct f_leak1 as (?&f_leak1). rewrite f_leak1 in H0.
        rewrite <- app_assoc in H0. apply app_inv_head in H0. inversion H0. clear H0.
        subst. reflexivity.
      + destruct f_reasonable1 as (f_branch1&_&_). specialize f_branch1 with (1 := H).
        destruct H as (?&H). rewrite <- app_assoc in H.
        destruct f_reasonable2 as (f_branch2&_&_).
        destruct H0 as (?&H0). rewrite <- app_assoc in H0.
        epose proof (f_branch1 _) as f_branch1. Unshelve. all: cycle 1.
        { eexists. eassumption. }
        destruct f_branch1 as (?&f_branch1). rewrite f_branch1 in H0.
        rewrite <- app_assoc in H0. apply app_inv_head in H0. inversion H0. subst. clear H0.
        erewrite Hsame. all: cycle 1.
        { eexists. rewrite <- app_assoc. eassumption. }
        destruct f_reasonable3 as (f_branch3&_&_). specialize (f_branch3 l val).
        epose proof (f_branch3 _ _) as f_branch3. Unshelve. all: cycle 1.
        { eexists. rewrite <- app_assoc. eassumption. }
        { eexists. eassumption. }
        destruct f_branch3 as (?&f_branch3). rewrite f_branch3 in H. rewrite <- app_assoc in H.
        apply app_inv_head in H. inversion H. subst. reflexivity.
  Qed.

  Fixpoint predictor_of_fun o (f : (list event -> B) -> list event) (k : list event) : qevent :=
    match k with
    | nil => match f o with
            | branch _ :: _ => qbranch
            | leak x :: _ => qleak x
            | nil => qend
            end
    | e :: k' =>
        predictor_of_fun (fun k => o (e :: k)) (fun o(*assumes no e*) => match f (fun k_(*assumes e*) =>
                                                           match k_ with
                                                           | nil =>
                                                               match e with
                                                               | leak _ => B_inhabited
                                                               | branch b => b
                                                               end
                                                           | _ :: k_' => o k_'
                                                           end) with
                                                | _ :: k'_ => k'_
                                                | _ => nil (*garbage*)
                                                end)
          k'
    end.

  Lemma reasonable_more_ext f o1 o1' o2 o2' :
    f o1' = f o1 ->
    f o2' = f o2 ->
    (forall k b1, prefix (k ++ [branch b1]) (f o2) -> o2' k = o2 k) ->
    fun_reasonable' f o1 o2 ->
    fun_reasonable' f o1' o2'.
  Proof.
    intros. cbv [fun_reasonable'] in *. repeat rewrite H, H0. intuition.
    erewrite H1; eauto.
  Qed.

  Lemma reasonable_start o1 o2 f :
    fun_reasonable' f o1 o1 ->
    fun_reasonable' f o1 o2 ->
    o1 [] = o2 [] ->
    forall e k1,
    f o1 = e :: k1 ->
    exists k2, f o2 = e :: k2.
  Proof.
    intros H0 H1 H2 e k1 H3. destruct e.
    - destruct H1 as (_&Hleak&_). specialize (Hleak nil val). simpl in Hleak.
      specialize (Hleak ltac:(eexists; rewrite H3; reflexivity) ltac:(eexists; reflexivity)).
      destruct Hleak as (?&Hleak). rewrite Hleak. eexists. reflexivity.
    - destruct H1 as (Hbranch&_&_). specialize (Hbranch nil val). simpl in Hbranch.
      specialize (Hbranch ltac:(eexists; rewrite H3; reflexivity) ltac:(eexists; reflexivity)).
      destruct Hbranch as (?&Hbranch). rewrite Hbranch. rewrite <- H2.
      destruct H0 as (Hbranch0&_&_). specialize (Hbranch0 nil val). simpl in Hbranch0.
      specialize (Hbranch0 ltac:(eexists; rewrite H3; reflexivity) ltac:(eexists; reflexivity)).
      destruct Hbranch0 as (?&Hbranch0). rewrite Hbranch0 in H3. inversion H3. subst.
      eexists. reflexivity.
  Qed.

  Lemma fun_reasonable_other (possible : _ -> Prop) f x :
    fun_reasonable (fun o => exists k, possible k /\ compat o k) f ->
    fun_reasonable
    (fun o' : list event -> B => exists k, possible (x :: k) /\ compat o' k)
    (fun o1 : list event -> B =>
     match
       f (fun k_ : list event => match k_ with
                              | [] => match x with
                                     | branch b => b
                                     | _ => B_inhabited
                                     end
                                 | _ :: k_' => o1 k_'
                                 end)
     with
     | [] => []
     | _ :: k'_ => k'_
     end).
  Proof.
    intros H. intros o1 o2 Ho1 Ho2. fwd.
    set (o1' := (fun k_ => match k_ with | [] => match x with
                                     | branch b => b
                                     | _ => B_inhabited
                                     end | _ :: k_' => o1 k_' end)).
    set (o2' := (fun k_ => match k_ with | [] => match x with
                                     | branch b => b
                                     | _ => B_inhabited
                                     end | _ :: k_' => o2 k_' end)).
    pose proof (H o1' o2') as Ho1'o2'.
    eassert _ as p1; [|eassert _ as p2; [|specialize (Ho1'o2' p1 p2)]].
    { eexists. split; [exact Ho1p0|]. destruct x.
      - constructor. assumption.
      - constructor; [reflexivity|]. simpl. assumption. }
    { eexists. split; [exact Ho2p0|]. destruct x.
      - constructor. assumption.
      - constructor; [reflexivity|]. simpl. assumption. }
    pose proof (H o1' o1' ltac:(assumption) ltac:(assumption)) as Ho1'o1'.
    pose proof (reasonable_start o1' o2' _ ltac:(eassumption) ltac:(eassumption) ltac:(reflexivity)) as Hstart.
    split; [|split]. 
    - fold o1'. fold o2'.
      destruct Ho1'o2' as (Hbranch&_&_). intros k1 b1 H1 H2.
      destruct H1 as (?&H1). destruct H2 as (?&H2).
      destruct (f o1') eqn:Eo1.
      { rewrite <- app_assoc in H1. apply app_cons_not_nil in H1. destruct H1. }
      subst. specialize (Hstart _ _ eq_refl). fwd. rewrite Hstart in Hbranch.
      edestruct Hbranch as (?&Hbranch').
      { eexists. do 2 rewrite <- app_assoc. simpl.
        match goal with | |- context[e :: ?x] => replace (e :: x) with ([e] ++ x) by reflexivity end.
        rewrite (app_assoc [e]). reflexivity. }
      { eexists. reflexivity. }
      do 2 rewrite <- app_assoc in Hbranch'. inversion Hbranch'. clear Hbranch'.
      Search (_ ++ _ = _ ++ _ -> _ = _). apply app_inv_head in H1. subst. eexists.
      rewrite <- app_assoc. reflexivity.
    - fold o1'. fold o2'.
      destruct Ho1'o2' as (_&Hleak&_). intros k1 b1 H1 H2.
      destruct H1 as (?&H1). destruct H2 as (?&H2).
      destruct (f o1') eqn:Eo1.
      { rewrite <- app_assoc in H1. apply app_cons_not_nil in H1. destruct H1. }
      subst. specialize (Hstart _ _ eq_refl). fwd. rewrite Hstart in Hleak.
      edestruct Hleak as (?&Hleak').
      { eexists. do 2 rewrite <- app_assoc. simpl.
        match goal with | |- context[e :: ?x] => replace (e :: x) with ([e] ++ x) by reflexivity end.
        rewrite (app_assoc [e]). reflexivity. }
      { eexists. reflexivity. }
      do 2 rewrite <- app_assoc in Hleak'. inversion Hleak'. clear Hleak'.
      apply app_inv_head in H1. subst. eexists.
      rewrite <- app_assoc. reflexivity.
    - fold o1'. fold o2'. destruct Ho1'o2' as (_&_&Hend). destruct (f o1').
      { specialize (Hend ltac:(eexists; reflexivity)). rewrite <- Hend. reflexivity. }
      specialize (Hstart _ _ eq_refl). fwd. intros (?&Hpre). subst.
      rewrite Hstart in Hend. specialize (Hend ltac:(eexists; reflexivity)).
      inversion Hend. do 2 rewrite <- H1. reflexivity.
  Qed.

  (*all of this nonsense is just because we allow f to behave arbitrarily badly when
    given a non-possible oracle as input.*)
  Lemma extend_or_not {A : Type} (possible : _ -> Prop) :
    exists f, forall (k : list A), (exists k', possible (k ++ k')) -> possible (k ++ f k).
  Proof. Admitted.
  
  Lemma predictor_from_nowhere f (possible : _ -> Prop) :
    fun_reasonable (fun o => exists k, possible k /\ compat o k) f ->
    exists pred,
    forall k,
      possible k ->
      predicts pred k <-> (forall A, (compat A k -> k = f A)).
  Proof.
    intros f_reasonable.
    destruct (extend_or_not possible) as (extend&Hextend).
    remember (fun k => oracle_of_trace (k ++ extend k)) as fn.
    assert (forall k, (exists k', possible (k ++ k')) -> (exists k', possible (k ++ k') /\ compat (fn k) (k ++ k'))) as Hfn.
    { intros k H. specialize (Hextend k H). fwd. exists (extend k). intuition.
      subst. apply oracle_of_trace_works. }
    clear Hextend Heqfn extend.
    exists (fun k => predictor_of_fun (fn k) f k).    
    intros k Hk. split.
    - intros Hpred A Hcompat.
      revert possible Hk fn Hfn f f_reasonable Hpred.
      induction Hcompat; intros possible Hk fn Hfn f f_reasonable Hpred.
      + inversion Hpred. clear Hpred. subst. cbv [predictor_of_fun] in H. simpl in H.
        destruct (f _) eqn:E; cycle 1. { destruct e; discriminate H. }
        specialize (Hfn nil). specialize (Hfn ltac:(exists nil; assumption)).
        simpl in Hfn.
        eassert _ as k0_poss; [|eassert _ as k_poss; [|pose proof (f_reasonable (fn []) o k0_poss k_poss) as Hk0o]].
        { apply Hfn. }
        { exists nil. intuition. constructor. }
        destruct Hk0o as (_&_&f_end).
        rewrite E in f_end. apply f_end. eexists. reflexivity.
      + inversion Hpred. subst. clear Hpred.
        specialize (IHHcompat (fun k => possible (branch (o []) :: k))).
        specialize IHHcompat with (4 := H4). simpl in IHHcompat.
        specialize (IHHcompat ltac:(assumption)).
        eassert _ as garbage. 2: specialize (IHHcompat garbage).
        { intros. fwd. specialize (Hfn (branch (o []) :: k0) ltac:(eexists; eassumption)).
          fwd. clear H. eexists. split; [eassumption|]. simpl in Hfnp1. inversion Hfnp1.
          subst. apply H5. }
        epose proof (IHHcompat (fun_reasonable_other _ _ _ ltac:(eassumption))) as IHHcompat.
        clear garbage.
        Search f. simpl in H3.
        epose proof (f_reasonable (fn []) o _ _) as fn_o. Unshelve. all: cycle 1.
        { simpl. specialize (Hfn nil ltac:(eexists; eassumption)). fwd. eauto. }
        { simpl. exists (branch (o []) :: k). intuition. constructor; [reflexivity|].
          assumption. }
        destruct (f (fn [])) eqn:E; try discriminate H3. destruct e; try discriminate H3.
        destruct fn_o as (Hbranch&_&_). specialize (Hbranch nil val ltac:(eexists; simpl; eassumption) ltac:(eexists; reflexivity)).
        destruct Hbranch as (?&Hbranch). simpl in Hbranch. rewrite Hbranch. f_equal.
        subst. erewrite reasonable_ext in Hbranch.
        -- rewrite Hbranch. reflexivity.
        -- apply f_reasonable.
           ++ eexists. split; [exact Hk|]. constructor; [reflexivity|]. assumption.
           ++ eexists. split; [exact Hk|]. constructor; [reflexivity|]. assumption.
        -- apply f_reasonable.
           ++ eexists. split; [exact Hk|]. constructor; [reflexivity|]. assumption.
           ++ eexists. split; [exact Hk|]. constructor; [reflexivity|]. assumption.
        -- apply f_reasonable.
           ++ eexists. split; [exact Hk|]. constructor; [reflexivity|]. assumption.
           ++ eexists. split; [exact Hk|]. constructor; [reflexivity|]. assumption.
        -- intros. move Hcompat at bottom. simpl. destruct H as (?&H).
           destruct k; [reflexivity|]. rewrite Hbranch in H. inversion H. subst.
           reflexivity.
     + inversion Hpred. subst. clear Hpred.
        specialize (IHHcompat (fun k => possible (leak l :: k))).
        specialize IHHcompat with (4 := H3). simpl in IHHcompat.
        specialize (IHHcompat ltac:(assumption)).
        eassert _ as garbage. 2: specialize (IHHcompat garbage).
        { intros. fwd. specialize (Hfn (leak l :: k0) ltac:(eexists; eassumption)).
          fwd. clear H. eexists. split; [eassumption|]. simpl in Hfnp1. inversion Hfnp1.
          subst. apply H1. }
        epose proof (IHHcompat (fun_reasonable_other _ _ _ ltac:(eassumption))) as IHHcompat.
        clear garbage.
        Search f. simpl in H2.
        epose proof (f_reasonable (fn []) o _ _) as fn_o. Unshelve. all: cycle 1.
        { simpl. specialize (Hfn nil ltac:(eexists; eassumption)). fwd. eauto. }
        { simpl. exists (leak l :: k). intuition. constructor.
          assumption. }
        destruct (f (fn [])) eqn:E; try discriminate H2. destruct e; try discriminate H2.
        inversion H2. subst. clear H2.
        destruct fn_o as (_&Hleak&_). specialize (Hleak nil l ltac:(eexists; simpl; eassumption) ltac:(eexists; reflexivity)).
        destruct Hleak as (?&Hleak). simpl in Hleak. rewrite Hleak. f_equal.
        subst. erewrite reasonable_ext in Hleak.
        -- rewrite Hleak. reflexivity.
        -- apply f_reasonable.
           ++ eexists. split; [exact Hk|]. constructor. assumption.
           ++ eexists. split; [exact Hk|]. constructor. assumption.
        -- apply f_reasonable.
           ++ eexists. split; [exact Hk|]. constructor. assumption.
           ++ eexists. split; [exact Hk|]. constructor. assumption.
        -- apply f_reasonable.
           ++ eexists. split; [exact Hk|]. constructor. assumption.
           ++ eexists. split; [exact Hk|]. constructor. assumption.
        -- intros. move Hcompat at bottom. simpl. destruct H as (?&H).
           destruct k.
           { simpl in H. rewrite Hleak in H. inversion H. }
           rewrite Hleak in H. inversion H. subst. reflexivity.
    - intros H.
      revert possible f f_reasonable fn Hfn Hk H.
      induction k; intros possible f f_reasonable fn Hfn Hk H.
      + constructor. simpl. rewrite <- H. 1: reflexivity. constructor.
      + constructor.
        -- specialize (Hfn nil ltac:(eexists; eassumption)). simpl in Hfn.
           specialize (H _ (oracle_of_trace_works _)).
           epose proof (f_reasonable (oracle_of_trace (a :: k)) (fn []) _ _) as H'.
           Unshelve. all: cycle 1.
           { cbv beta. exists (a :: k). intuition. apply oracle_of_trace_works. }
           { simpl. assumption. }
           simpl. destruct a.
           ++ destruct H' as (_&Hleak&_). specialize (Hleak nil val).
              rewrite <- H in Hleak. specialize (Hleak ltac:(eexists; reflexivity) ltac:(eexists; reflexivity)).
              destruct Hleak as (?&Hleak). rewrite Hleak. reflexivity.
           ++ destruct H' as (Hbranch&_&_). specialize (Hbranch nil val).
              rewrite <- H in Hbranch. specialize (Hbranch ltac:(eexists; reflexivity) ltac:(eexists; reflexivity)).
              destruct Hbranch as (?&Hbranch). rewrite Hbranch. reflexivity.
        -- simpl. specialize (IHk (fun k => possible (a :: k))). apply IHk.
           ++ apply fun_reasonable_other. assumption.
           ++ intros. specialize (Hfn (a :: k0) ltac:(assumption)).
              fwd. clear H0. eexists. split; [eassumption|]. simpl in Hfnp1.
              inversion Hfnp1; assumption.
           ++ assumption.
           ++ intros A HA. rewrite <- H.
              --- reflexivity.
              --- destruct a.
                  +++ constructor. assumption.
                  +++ constructor; [reflexivity|]. assumption.
  Qed.
End ShortTheorems.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Transitive_Closure.
Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique coqutil.Byte.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Properties.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Export bedrock2.Memory.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Classes.Morphisms.

Require Import Coq.Wellfounded.Union.
Require Import Relation_Operators.
Require Import Relation_Definitions.
Require Import Transitive_Closure.
Require Import Coq.Logic.ChoiceFacts.

Require Import Coq.Lists.List.
Require Import equiv.EquivDefinitions.

Module possible.
Section possible.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Context (e: env).
  
  Inductive possible :
    cmd -> trace -> io_trace -> mem -> locals  ->
    trace -> io_trace -> mem -> locals -> Prop :=
  | skip
      k t m l
    : possible cmd.skip k t m l k t m l
  | set x e
      m l
      k t v k' (_ : eval_expr m l e k = Some (v, k'))
    : possible (cmd.set x e) k t m l k' t m (map.put l x v)
  | unset x
      k t m l
    : possible (cmd.unset x) k t m l k t m (map.remove l x)
  | store sz ea ev
      k t m l
      a k' (_ : eval_expr m l ea k = Some (a, k'))
      v k'' (_ : eval_expr m l ev k' = Some (v, k''))
      m' (_ : Memory.store sz m a v = Some m')
    : possible (cmd.store sz ea ev) k t m l (leak_word a :: k'') t m' l
  | stackalloc x n body
      k t mSmall l k' t' mSmall' l'
      (_ : Z.modulo n (bytes_per_word width) = 0)
      (_ : exists a mStack mCombined,
          anybytes a n mStack /\
            map.split mCombined mSmall mStack /\
            exists mCombined',
              possible body (Leakage.branch a :: k) t mCombined (map.put l x a)
                k' t' mCombined' l' /\
                exists mStack',
                  anybytes a n mStack' /\
                    map.split mCombined' mSmall' mStack')
    : possible (cmd.stackalloc x n body) k t mSmall l k' t' mSmall' l'
            
  | if_true k t m l e c1 c2 k'' t' m' l'
      v k' (_ : eval_expr m l e k = Some (v, k'))
      (_ : word.unsigned v <> 0)
      (_ : possible c1 (leak_bool true :: k') t m l k'' t' m' l')
    : possible (cmd.cond e c1 c2) k t m l k'' t' m' l'
  | if_false e c1 c2 k'' t' m' l'
      k t m l
      v k' (_ : eval_expr m l e k = Some (v, k'))
      (_ : word.unsigned v = 0)
      (_ : possible c2 (leak_bool false :: k') t m l k'' t' m' l')
    : possible (cmd.cond e c1 c2) k t m l k'' t' m' l'
  | seq c1 c2
      k t m l k' t' m' l' k'' t'' m'' l''
      (_ : possible c1 k t m l k' t' m' l')
      (_ : possible c2 k' t' m' l' k'' t'' m'' l'')
    : possible (cmd.seq c1 c2) k t m l k'' t'' m'' l''
  | while_false e c
      k t m l
      v k' (_ : eval_expr m l e k = Some (v, k'))
      (_ : word.unsigned v = 0)
    : possible (cmd.while e c) k t m l (leak_bool false :: k') t m l
  | while_true e c k'' t' m' l' k''' t'' m'' l''
      k t m l
      v k' (_ : eval_expr m l e k = Some (v, k'))
      (_ : word.unsigned v <> 0)
      (_ : possible c (leak_bool true :: k') t m l k'' t' m' l')
      (_ : possible (cmd.while e c) k'' t' m' l' k''' t'' m'' l'')
    : possible (cmd.while e c) k t m l k''' t'' m'' l''
  | call binds fname arges k'' t' m' st1 l'
      k t m l
      params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
      args k' (_ : evaluate_call_args_log m l arges k = Some (args, k'))
      lf (_ : map.of_list_zip params args = Some lf)
      (_ : possible fbody (leak_unit :: k') t m lf k'' t' m' st1)
      (_ : exists retvs, map.getmany_of_list st1 rets = Some retvs /\
                      map.putmany_of_list_zip binds retvs l = Some l')
    : possible (cmd.call binds fname arges) k t m l k'' t' m' l'
  | interact binds action arges
      k t m l l' m'
      mKeep mGive mid (_: map.split m mKeep mGive)
      args k' (_ :  evaluate_call_args_log m l arges k = Some (args, k'))
      mReceive resvals klist
      (_ : ext_spec t mGive action args mid)
      (_ : forall mid, ext_spec t mGive action args mid -> mid mReceive resvals klist)
      (_ : map.putmany_of_list_zip binds resvals l = Some l' /\
             map.split m' mKeep mReceive)
    : possible (cmd.interact binds action arges) k t m l (leak_list klist :: k')%list (((mGive, action, args), (mReceive, resvals)) :: t) m' l'
  .
End possible.
End possible. Notation possible := possible.possible.

Ltac invert_stuff :=
  repeat match goal with
    | H1: ?e = Some (?x1, ?y1, ?z1), H2: ?e = Some (?x2, ?y2, ?z2) |- _ =>
        replace x2 with x1 in * by congruence;
        replace y2 with y1 in * by congruence;
        replace z2 with z1 in * by congruence;
        clear x2 y2 z2 H2
    end;
  repeat match goal with
    | H1: ?e = Some (?x1, ?z1), H2: ?e = Some (?x2, ?z2) |- _ =>
        replace x2 with x1 in * by congruence;
        replace z2 with z1 in * by congruence;
        clear x2 z2 H2
    end;
  repeat match goal with
    | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
        replace v2 with v1 in * by congruence; clear H2
    end;
  repeat match goal with
    | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
        replace v2 with v1 in * by congruence; clear H2
    end.

Section possible_vs_exec.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.
  
  Lemma possible_to_exec e s k t m l post :
    exec_nondet e s k t m l post ->
    forall k' t' m' l', 
    possible e s k t m l k' t' m' l' ->
    post k' t' m' l'.
  Proof.
    intros Hexec. induction Hexec; intros kF tF mF lF H'; try solve [inversion H'; subst; invert_stuff; auto].
    - inversion H'. clear H'. subst. fwd.
      specialize (H1 _ _ _ ltac:(congruence) H14p0 H14p1 _ _ _ _ H14p2p0). fwd.
      lazymatch goal with
      | A: map.split ?a ?y ?z, B: map.split ?a ?y' ?z' |- _ =>
        specialize @map.split_diff with (4 := A) (5 := B) as Q
      end.
      edestruct Q; try typeclasses eauto. 2: subst; eauto 10.
      eapply anybytes_unique_domain; eassumption.
    - inversion H'; try congruence. subst. invert_stuff. apply IHHexec. assumption.
    - inversion H'; try congruence. subst. invert_stuff. apply IHHexec. assumption.
    - inversion H'. subst. eauto.
    - inversion H'; congruence.
    - inversion H'; try congruence. subst. invert_stuff. eauto.
    - inversion H'. subst. fwd. invert_stuff. apply IHHexec in H17. apply H2 in H17.
      fwd. invert_stuff. assumption.
    - inversion H'. subst. invert_stuff.
      pose proof ext_spec.unique_mGive_footprint as Q.
      specialize Q with (1 := H1) (2 := H8).
      destruct (map.split_diff Q H H6). subst mKeep0 mGive0.
      apply H17 in H1. apply H2 in H1. fwd. invert_stuff. eauto.
  Qed.
      
  Lemma intersect_two e s k t m l post1 post2 :
    exec_nondet e s k t m l post1 ->
    exec_nondet e s k t m l post2 ->
    exec_nondet e s k t m l (fun k' t' m' l' => post1 k' t' m' l' /\ post2 k' t' m' l').
  Proof. Admitted.

  Lemma possible_to_exec2 e s k t m l post :
    exec_nondet e s k t m l post ->
    exec_nondet e s k t m l (possible e s k t m l).
  Proof.
    intros H. induction H.
    - econstructor; eauto. econstructor.
    - econstructor; eauto. econstructor; eauto.
    - econstructor; eauto. econstructor; eauto.
    - econstructor; eauto. econstructor; eauto.
    - econstructor; eauto. intros. eapply weaken. 1: eapply intersect_two.
      1: eapply H0; eauto. 1: eapply H1; eauto. simpl. intros. fwd.
      do 2 eexists. intuition eauto. econstructor; eauto. exists a, mStack, mCombined.
      intuition. exists m'. intuition. exists mStack'. auto.
    - eapply if_true; eauto. eapply weaken. 1: eapply IHexec. intros.
      eapply possible.if_true; eauto.
    - eapply if_false; eauto. eapply weaken. 1: eapply IHexec. intros.
      eapply possible.if_false; eauto.
    - econstructor. 1: eapply intersect_two. 1: eapply H. 1: eapply IHexec.
      simpl. intros. fwd. eapply weaken. 1: eapply H1; eauto. intros.
      econstructor; eauto.
    - eapply while_false; eauto. econstructor; eauto.
    - eapply while_true. 1,2: eauto. 1: eapply intersect_two. 1: eapply H1.
      1: eapply IHexec. simpl. intros. fwd. eapply weaken. 1: eapply H3; eauto.
      intros. eapply possible.while_true; eauto.
    - econstructor. 1,2,3: eauto. 1: eapply intersect_two. 1: eapply H2. 1: eapply IHexec.
      simpl. intros. fwd. apply H3 in H4p0. fwd. eexists. intuition eauto.
      eexists. intuition eauto. econstructor; eauto.
    - econstructor. 3: eapply ext_spec.intersect; eauto. 1,2: eauto. simpl. intros.
      pose proof H1 as H1'.
      apply H3 in H1. apply H2 in H1. fwd. exists l'. intuition. econstructor; eauto.
  Qed.
    
  Lemma possible_iff_exec e s k t m l post0 post :
    exec_nondet e s k t m l post0 ->
    exec_nondet e s k t m l post <-> (forall k' t' m' l', possible e s k t m l k' t' m' l' -> post k' t' m' l').
  Proof.
    intros. split.
    - intros. eapply possible_to_exec; eassumption.
    - intros. eapply weaken. 1: eapply possible_to_exec2; eassumption. assumption.
  Qed.

  Lemma possible_traces_sane e s k t m l k1 t1 m1 l1 k2 t2 m2 l2 evt k' :
    possible e s k t m l k1 t1 m1 l1 ->
    possible e s k t m l k2 t2 m2 l2 ->
    (exists k1_, k1 = k1_ ++ evt :: k') ->
    (exists k2_, k2 = k2_ ++ k') ->
    exists evt' k2_, k2 = k2_ ++ evt' :: k' /\ Leakage.q evt = Leakage.q evt'.
  Proof.
    intros poss1. induction poss1. 5: { intros poss2 pre1 pre2; (inversion poss2; try congruence; []); clear poss2; subst; invert_stuff; fwd; try solve [do 2 eexists; split; [eassumption|reflexivity]].
    - 
  
End possible_vs_exec.  
    Import List.ListNotations.

    Definition possible_trace e s k t m l mc k' := exists t' m' l' mc', strongest_post e s k t m l mc k' t' m' l' mc'.

    Lemma id_is_nil {A : Type} (l1 l2 : list A) :
      l1 ++ l2 = l2 -> l1 = nil.
    Proof. intros. eapply app_inv_tail. simpl. eassumption. Qed.

    Lemma rev_nil_nil {A : Type} (l : list A) :
      rev l = nil -> l = nil.
    Proof. intros. rewrite <- (rev_involutive l). rewrite H. reflexivity. Qed.

    Lemma rev_inj {A : Type} (l1 l2 : list A) :
      rev l1 = rev l2 -> l1 = l2.
    Proof. intros. rewrite <- (rev_involutive l1). rewrite H. apply rev_involutive. Qed.
    
     Lemma trace_is_sane e s k t m l mc k1' k2' k' evt post0 :
       exec_nondet e s k t m l mc post0 ->
       possible_trace e s k t m l mc k1' ->
       possible_trace e s k t m l mc k2' ->
       (exists k1'', k1' = k1'' ++ evt :: k') ->
       (exists k2'', k2' = k2'' ++ k') ->
       exists evt' k2'', k2' = k2'' ++ evt' :: k' /\ Leakage.q evt = Leakage.q evt'.
     Proof.
       intros nontriv. induction nontriv.
       - intros poss1 poss2 pre1 pre2.
         cbv [possible_trace strongest_post] in poss1, poss2. fwd.
         epose proof (poss1 (exactly _ _ _ _ _) _) as poss1. Unshelve. all: cycle 1.
         { econstructor. cbv [exactly]. eauto. }
         epose proof (poss2 (exactly _ _ _ _ _) _) as poss2. Unshelve. all: cycle 1.
         { econstructor. cbv [exactly]. eauto. }
         cbv [exactly] in poss1, poss2. fwd. destruct pre1, pre2. subst.
         exists evt. cbv [prefix]. eauto.
       - intros poss1 poss2 pre1 pre2.
         cbv [possible_trace strongest_post] in poss1, poss2. fwd.
         epose proof (poss1 (exactly _ _ _ _ _) _) as poss1. Unshelve. all: cycle 1.
         { econstructor; eauto. cbv [exactly]. eauto. }
         epose proof (poss2 (exactly _ _ _ _ _) _) as poss2. Unshelve. all: cycle 1.
         { econstructor; eauto. cbv [exactly]. eauto. }
         cbv [exactly] in poss1, poss2. fwd. destruct pre1, pre2. subst.
         exists evt. cbv [prefix]. eauto.
       - intros poss1 poss2 pre1 pre2.
         cbv [possible_trace strongest_post] in poss1, poss2. fwd.
         epose proof (poss1 (exactly _ _ _ _ _) _) as poss1. Unshelve. all: cycle 1.
         { econstructor; eauto. cbv [exactly]. eauto. }
         epose proof (poss2 (exactly _ _ _ _ _) _) as poss2. Unshelve. all: cycle 1.
         { econstructor; eauto. cbv [exactly]. eauto. }
         cbv [exactly] in poss1, poss2. fwd. destruct pre1, pre2. subst.
         exists evt. cbv [prefix]. eauto.
       - intros poss1 poss2 pre1 pre2.
         cbv [possible_trace strongest_post] in poss1, poss2. fwd.
         epose proof (poss1 (exactly _ _ _ _ _) _) as poss1. Unshelve. all: cycle 1.
         { econstructor; eauto. cbv [exactly]. eauto. }
         epose proof (poss2 (exactly _ _ _ _ _) _) as poss2. Unshelve. all: cycle 1.
         { econstructor; eauto. cbv [exactly]. eauto. }
         cbv [exactly] in poss1, poss2. fwd. destruct pre1, pre2. subst.
         exists evt. cbv [prefix]. eauto.
       - intros poss1 poss2 pre1 pre2.
         cbv [possible_trace strongest_post] in poss1, poss2. fwd.
         epose proof (poss1 (fun k'1 t'1 m'1 l'1 mc'1 => exists a mStack mCombined,
                                 anybytes a n mStack /\
                                   map.split mCombined mSmall mStack /\
                                   exists k1'_, k1' = branch a :: k1'_)
                                 _) as poss1. Unshelve. all: cycle 1.
         { econstructor; eauto. intros. Search exec. eapply weaken. 1: eauto. simpl. intros.
           fwd. do 2 eexists. intuition eauto. }
         simpl in poss1.
         epose proof (poss2 _ _) as poss2. Unshelve. all: cycle 1.
         { econstructor; eauto. }
         cbv [exactly] in poss1, poss2. fwd.
         assert (rev k1_' ++ k = rev k2_' ++ k) as H' by (rewrite poss1p0, poss2p0; reflexivity).
         clear poss1p0 poss2p0.
         apply app_inv_tail in H'. apply rev_inj in H'. subst.
         exists evt. auto.
         
         cbv [exactly] in poss1. fwd.
         apply id_is_nil in poss1p0.
         apply rev_nil_nil in poss1p0.
         subst. destruct pre as (?&pre). rewrite <- app_assoc in pre.
         Search (nil = _ ++ _ :: _). apply app_cons_not_nil in pre. destruct pre.
         revert H0p0. assert ((rev k1' ++ k = k) = (rev k1' ++ k = [] ++ k)) as -> by reflexivity.
         subst. idtac.
                                                      eassert _ as Ex. 2: specialize H0 with (1 := Ex). simpl in H0.
       poss1 poss2 prefix. cbv [possible_trace] in poss1, poss2. fwd.
       
       cbv [strongest_post] in poss1, poss2. specialize poss1 with (1 := nontriv).
       
       
b
    Print fun_reasonable.
    Lemma reasonable e s k t m l mc f :
      exec_nondet e s k t m l mc (fun k' t' m' l' mc' => exists k'',
                                      k' = k'' ++ k /\
                                        (forall A, compat A (rev k'') -> (rev k'') = f A)) ->
      let possible_k := (fun k' => exists t' m' l' mc', strongest_post e s k t m l mc (rev k' ++ k) t' m' l' mc') in
      fun_reasonable (fun o => exists k, possible_k k /\ compat o k) f.
    Proof.
      intros H. pose proof (exec_iff_impl_by_strongest_post _ _ _ _ _ _ _ _ H) as H0.
      rewrite H0 in H. clear H0.
      split; [|split].
      - fwd. apply H in H0p0, H1p0. fwd. apply app_inv_tail in H0p0p0, H1p0p0. subst.
        simpl. rewrite rev_involutive in *. specialize H0p0p1 with (1 := H0p1).
        specialize H1p0p1 with (1 := H1p1). subst. intros.
        rewrite <- compat'_iff_compat in H0p1. Check Leakage.compat'.

        
    Lemma oracles_to_predictors e s k t m l mc f :
      exec_nondet e s k t m l mc (fun k' t' m' l' mc' => exists k'',
                                      k' = k'' ++ k /\
                                        (forall A, compat A (rev k'') -> (rev k'') = f A)) ->
      exists pred,
        exec_nondet e s k t m l mc (fun k' t' m' l' mc' => exists k'',
                                        k' = k'' ++ k /\
                                          predicts pred (rev k'')).
    Proof.
      intros H. epose proof (exec_iff_impl_by_strongest_post _ _ _ _ _ _ _ _ H) as H0.
      rewrite H0 in H. eenough (exists pred, _) as H1.
      { destruct H1 as (pred&H1). exists pred. rewrite H0. exact H1. }
      clear H0. pose proof (@predictor_from_nowhere leakage word (word.of_Z 0)) as H'.
      specialize (H' f (fun k' => exists t' m' l' mc', strongest_post e s k t m l mc (rev k' ++ k) t' m' l' mc')).
      simpl in H'. eassert _ as f_reasonable. 2: specialize (H' f_reasonable).
      { 


    Axiom fun_reasonable : forall (f: (trace -> event) -> trace) (A B : trace -> event), Prop.

    Definition possible e s k t m l mc A :=
      exists k' t' m' l' mc', strongest_post e s k t m l mc k' t' m' l' mc' /\ compat A k'.

    Axiom possible' : forall (A : trace -> event), Prop.
    
    Lemma predictor_from_nowhere f :
      (forall A B, possible' A -> possible' B -> fun_reasonable f A B) ->
      exists pred,
      forall k,
        predicts pred k <-> (forall A, possible' A -> (compat A k -> k = f A)).
    Admitted.

    Lemma funs_reasonable e s k t m l mc f A B :
      possible e s k t m l mc A ->
      possible e s k t m l mc B ->
      fun_reasonable f A B.
    Proof.
      intros. cbv [fun_reasonable].

    Check exec_nondet.

    Fixpoint tree_of_trace (k : trace) : trace_tree. Admitted.

    Lemma tree_of_trace_works k : path k (tree_of_trace k). Admitted.


    Definition id (X: Type) := X.
    Opaque id.
    Definition id' {X : Type} (x: X) : id X := x.
    
    Ltac subst_exprs :=
  repeat match goal with
    | H : eval_expr _ _ _ _ _ = Some _ |- _ =>
        pose proof (id' H); apply eval_expr_extends_trace in H; destruct H as [? [? ?] ]; subst
    | H : evaluate_call_args_log _ _ _ _ _ = Some _ |- _ =>
        pose proof (id' H); apply evaluate_call_args_log_extends_trace in H; destruct H as [? [? ?] ]; subst
    end; cbv [id] in *.
    
    Lemma pred_ct_impl_tree_ct e s k t m l mc (pred : trace -> qevent) P :
      exec_nondet e s k t m l mc (fun k' _ _ _ _ => P k' -> exists k'', k' = k'' ++ k /\ predicts pred (rev k'')) ->
      exists tree,
        exec_nondet e s k t m l mc (fun k' _ _ _ _ => P k' -> exists k'', k' = k'' ++ k /\ path k'' tree).
    Proof.
      remember (fun k _ _ _ _ => _) as post.
      eassert (Hpost : forall k t m l mc, post k t m l mc -> _).
      { intros * H. subst. exact H. }
      clear Heqpost.
      intros H. revert pred P Hpost. induction H; intros pred P Hpost; repeat match goal with
                                                                     | H: _ |- _ => pose proof (Hpost _ _ _ _ _ H); clear H end; try clear Hpost post; fwd; subst_exprs; try
      (eexists (tree_of_trace _); econstructor; eauto; eexists; split; trace_alignment;
       try rewrite app_nil_r; apply tree_of_trace_works).
      4: { Abort.

    Lemma ct_impl_pred_ct e s k t m l mc 
