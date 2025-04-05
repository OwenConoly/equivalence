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

  Lemma fun_reasonable_other (possible : _ -> Prop) f x :
    (forall o1 o2, possible o1 ->
              (forall k b1, prefix (k ++ [branch b1]) (f o1) -> o2 k = o1 k) ->
              possible o2) ->
    fun_reasonable possible f ->
    fun_reasonable
    (fun o0' : list event -> B =>
     exists o1 : list event -> B,
       possible o1 /\ (forall k0 : list event, o1 (branch x :: k0) = o0' k0))
    (fun o1 : list event -> B =>
     match
       f (fun k_ : list event => match k_ with
                                 | [] => x
                                 | _ :: k_' => o1 k_'
                                 end)
     with
     | [] => []
     | _ :: k'_ => k'_
     end).
  Proof.
    intros Hposs H. intros o0 o1 Ho0 Ho1. fwd.
    pose proof (H o2 o3 ltac:(assumption) ltac:(assumption)) as Ho2o3.
    split; [|split].
    - intros. destruct Ho2o3 as (Ho2o3&_&_). specialize (Ho2o3 (branch x :: k) b1).
      destruct H0 as (?&H0). destruct (f (fun k_ => _)) eqn:E0.
      { destruct k; simpl in H0; discriminate H0. }
      eassert (f o2 = e::l).
      { rewrite <- E0. apply reasonable_ext.
        - apply H; [assumption|]. apply (Hposs o2 _ ltac:(assumption)).
          intros. destruct k0.
          + destruct H2 as (?&H2). simpl in H2.
            pose proof (H o2 o2 ltac:(assumption) ltac:(assumption)) as Ho2o2.
            destruct Ho2o2 as (Hbranch&_&_). specialize (Hbranch nil b0).
            edestruct Hbranch as (?&Hbranch').
            -- eexists. rewrite H2. reflexivity.
            -- eexists. reflexivity.
            -- simpl in Hbranch'. rewrite H2 in Hbranch'. inversion Hbranch'. subst.
               Search x.
               
          rewrite <- Ho0p1. 1,2,3: apply H. 3: apply H; assumption.
        - eapply reasonable_more_ext.
      replace (f o2) th (f _).
      subst. 
      destruct H1 as (?&H1). move E0 after H1. destruct (f (fun k_ => _)) eqn:E1.
      { destruct 
      

  Lemma predictor_from_nowhere f (possible : _ -> Prop) o :
    possible o ->
    fun_reasonable possible f ->
    exists pred,
    forall k,
      predicts pred k <-> (forall A, possible A -> (compat A k -> k = f A)).
  Proof.
    intros Ho f_reasonable. exists (predictor_of_fun o f). intros. split.
    - intros Hpred A Hposs Hcompat.
      revert possible Hposs o Ho f f_reasonable Hpred.
      induction Hcompat; intros possible Hposs o0 Ho0 f f_reasonable Hpred.
      + inversion Hpred. clear Hpred. subst. cbv [predictor_of_fun] in H. simpl in H.
        destruct (f _) eqn:E; cycle 1. { destruct e; discriminate H. }
        destruct (f_reasonable o0 o ltac:(assumption) ltac:(assumption)) as (_&_&f_end).
        rewrite E in f_end. apply f_end. eexists. reflexivity.
      + inversion Hpred. subst. clear Hpred. 
        simpl in H3. destruct (f o0) eqn:E; [discriminate H3|].
        destruct e; try discriminate H3. clear H3.
        pose proof f_reasonable as f_reasonable'.
        destruct (f_reasonable' o0 o ltac:(assumption) ltac:(assumption)) as (f_branch&_&_).
        epose proof (f_branch nil val _ _) as H.
        Unshelve. all: cycle 1.
        { eexists. simpl. rewrite E. reflexivity. }
        { eexists. reflexivity. }
        destruct H as [l' H]. simpl in H. rewrite H. f_equal.
        simpl in H4. specialize IHHcompat with (4 := H4).
        Check reasonableness_preserved'.
        epose proof (IHHcompat (fun o0' => exists o0, possible o0 /\ forall k, o0 (branch (o []) :: k) = o0' k) _ _ _) as IHHcompat.
        Unshelve. all: cycle 1.
        { simpl. exists o. auto. }
        { simpl. exists o0. auto. }
        { intros o1 o2 Ho1 Ho2. eapply reasonableness_preserved'.
          - fwd. specialize (f_reasonable' o4 o3 ltac:(assumption) ltac:(assumption)).
            eapply reasonable_more_ext. 4: exact f_reasonable'.
            + apply reasonable_ext.
            specialize (f_branch o A nil (o []) ltac:(exists l'; rewrite H; reflexivity)).
          specialize (f_branch ltac:(eexists; reflexivity)).

          ; cycle 1.
          { rewrite 
          apply reasonable_ext.
          - fwd. eapply f_reasonable'.
            + eexists. specialize (f_reasonable' o1 o2 Ho1 Ho2).
            intros. instantiate (1 := fun x => branch x). simpl.
          simpl in f_branch. apply f_branch. }
        subst. erewrite <- reasonable_ext. 1: rewrite H; reflexivity.
        1: assumption. intros. destruct k; [reflexivity|]. destruct H0 as (?&H0).
        rewrite H0 in H. inversion H. subst. reflexivity.
      + inversion Hpred. subst. clear Hpred. simpl in H3. 
        pose proof f_reasonable as f_reasonable'.
        destruct f_reasonable' as (_&f_leak&_).
        simpl in H2. destruct (f _) eqn:E; try discriminate H2.
        destruct e; inversion H2; subst; clear H2.
        epose proof (f_leak (fun _ => B_inhabited) o nil l _ _) as H.
        Unshelve. all: cycle 1.
        { eexists. simpl. rewrite E. reflexivity. }
        { eexists. reflexivity. }
        destruct H as [l' H]. simpl in H. rewrite H. f_equal.
        specialize IHHcompat with (2 := H3).
        Check reasonableness_preserved'.
        epose proof (IHHcompat (reasonableness_preserved' _ _ _ f_reasonable _)) as IHHcompat.
        Unshelve. all: cycle 2.
        { intros. instantiate (1 := fun x => leak l). simpl.
          specialize (f_leak o A nil l ltac:(exists l'; rewrite H; reflexivity)).
          specialize (f_leak ltac:(eexists; reflexivity)).
          simpl in f_leak. apply f_leak. }
        subst. erewrite <- reasonable_ext. 1: rewrite H; reflexivity.
        1: assumption. intros. destruct k.
        -- destruct H0 as (?&H0). rewrite H0 in H. simpl in H. inversion H.
        -- destruct H0 as (?&H0). rewrite H0 in H. simpl in H. inversion H. reflexivity.
    - intros. revert f f_reasonable H. induction k; intros f f_reasonable H.
      + constructor. simpl. specialize (H (fun _ => B_inhabited)).
        specialize (H ltac:(constructor)). rewrite <- H. reflexivity.
      + constructor.
        -- simpl. specialize (H _ (oracle_of_trace_works _)). destruct a.
           ++ destruct f_reasonable as (_&f_leak&_).
              epose proof (f_leak (oracle_of_trace (leak val :: k)) (fun _ => B_inhabited) nil val _ _) as f_leak.
              Unshelve. all: cycle 1.
              { eexists.  rewrite <- H. reflexivity. }
              { eexists. reflexivity. }
              destruct f_leak as (?&f_leak). simpl in f_leak. rewrite f_leak. reflexivity.
           ++ destruct f_reasonable as (f_branch&_&_).
              epose proof (f_branch (oracle_of_trace (branch val :: k)) (fun _ => B_inhabited) nil val _ _) as f_leak.
              Unshelve. all: cycle 1.
              { eexists.  rewrite <- H. reflexivity. }
              { eexists. reflexivity. }
              destruct f_leak as (?&f_leak). simpl in f_leak. rewrite f_leak. reflexivity.
        -- simpl. apply IHk.
           ++ eapply reasonableness_preserved'. 1: assumption. clear IHk.
              specialize (H _ (oracle_of_trace_works _)).
              destruct a.
              --- destruct f_reasonable as (_&f_leak&_). intros A.
                  specialize (f_leak (oracle_of_trace (leak val :: k)) A nil val).
                  epose proof (f_leak _ _) as f_leak.
                  Unshelve. all: cycle 2.
                  { rewrite <- H. exists k. reflexivity. }
                  { eexists. reflexivity. }
                  1: {  instantiate (1 := match a with
                                      | leak val => fun _ => leak val
                                      | _ => _
                                          end). simpl.  simpl in f_leak. apply f_leak. }
              --- simpl. destruct f_reasonable as (f_branch&_&_). intros A.
                  specialize (f_branch (oracle_of_trace (branch val :: k)) A nil val).
                  epose proof (f_branch _ _) as f_branch.
                  Unshelve. all: cycle 2.
                  { rewrite <- H. eexists. reflexivity. }
                  { eexists. reflexivity. }
                  { instantiate (1 := fun x => branch x). simpl. apply f_branch. }
           ++ intros. specialize (H (fun k' => match k' with
                                            | nil => (match a with
                                                     | branch x => x
                                                     | leak _ => B_inhabited
                                                     end)
                                            | _ :: k' => A k'
                                            end)).
              epose proof (H _) as H. Unshelve. all: cycle 1.
              { destruct a.
                - constructor. assumption.
                - constructor; [reflexivity|assumption]. }
              rewrite <- H. reflexivity.
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
Require Import bedrock2.MetricLogging.
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

Check exec_nondet.

Module UseExec.
  Section UseExec.
    Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
    Context {locals: map.map String.string word}.
    Context {env: map.map String.string (list String.string * list String.string * cmd)}.
    Context {ext_spec: ExtSpec}.

    Axiom fun_reasonable : forall (f: (trace -> event) -> trace) (A B : trace -> event), Prop.

    Definition strongest_post e s k t m l mc k' t' m' l' mc' :=
      exec_nondet e s k t m l mc (fun _ _ _ _ _ => True) /\
      forall P, exec_nondet e s k t m l mc P -> P k' t' m' l' mc'.

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

    Import List.ListNotations.

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
