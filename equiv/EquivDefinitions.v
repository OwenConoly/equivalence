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

Module Leakage.
  Section GeneralLeakageDefns.
    Context {L B : Type}.
    Context (B_inhabited : B).

    (*note that (list event) is the sort of leakage trace discussed in the paper.*)
    Inductive event :=
    | leak (val : L)
    | branch (val : B).

    Inductive qevent : Type :=
    | qleak (val : L)
    | qbranch
    | qend.

    Definition q (e : event) : qevent :=
      match e with
      | leak l => qleak l
      | branch b => qbranch
      end.

    Inductive trace_tree :=
    | tree_leaf
    | tree_leak (l : L) (rest : trace_tree)
    | tree_branch (rest : B -> trace_tree).

    (*Defn 4.1 of paper*)
    Definition predicts' (pred : list event -> qevent) (k : list event) :=
      (forall k1 x k2, k = k1 ++ leak x :: k2 -> pred k1 = qleak x)/\
        (forall k1 x k2, k = k1 ++ branch x :: k2 -> pred k1 = qbranch) /\
        pred k = qend.

    (*an equivalent inductive definition*)
    Inductive predicts : (list event -> qevent) -> list event -> Prop :=
    | predicts_nil f : f nil = qend -> predicts f nil
    | predicts_cons f e k : f nil = q e -> predicts (fun k_ => f (e :: k_)) k -> predicts f (e :: k).

    Inductive path : list event -> trace_tree -> Prop :=
    | path_leaf : path nil tree_leaf
    | path_leak k t l : path k t -> path (leak l :: k) (tree_leak l t)
    | path_branch k t b : path k (t b) -> path (branch b :: k) (tree_branch t).

    (*Definition 2.3 of the paper*)
    Definition compat' (oracle : list event -> B) (k : list event) :=
      forall k1 x k2, k = k1 ++ branch x :: k2 -> oracle k1 = x.

    (*an equivalent inductive definition*)
    Inductive compat : (list event -> B) -> list event -> Prop :=
    | compat_nil o : compat o nil
    | compat_cons_branch o k b : o nil = b -> compat (fun k_ => o (branch b :: k_)) k -> compat o (branch b :: k)
    | compat_cons_leak o k l : compat (fun k_ => o (leak l :: k_)) k -> compat o (leak l :: k).
  End GeneralLeakageDefns.
End Leakage.
  
(* BW is not needed on the rhs, but helps infer width *)
Definition io_event {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} : Type :=
  (mem * String.string * list word) * (mem * list word).

Inductive leakage {width: Z}{BW: Bitwidth width}{word: word.word width} :=
| leak_unit'
| leak_bool' (b : bool)
| leak_word' (w : word)
| leak_list' (l : list word).

Definition event {width: Z}{BW: Bitwidth width}{word: word.word width} : Type :=
  @Leakage.event leakage word.

Section WithIOEvent.
  Context {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte}.

  (*Definition of leakage trace, as in the paper.*)
  Definition trace : Type := list event.
  Definition leak := @Leakage.leak leakage word.
  Definition branch := @Leakage.branch leakage word.
  Definition leak_unit := leak leak_unit'.
  Definition leak_bool b := leak (leak_bool' b).
  Definition leak_word w := leak (leak_word' w).
  Definition leak_list l := leak (leak_list' l).
  Definition compat := (@Leakage.compat leakage word).
  Definition predicts := (@Leakage.predicts leakage word).
  Definition io_trace : Type := list io_event.
End WithIOEvent.

Definition ExtSpec{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} :=
  (* Given a trace of what happened so far,
     the given-away memory, an action label and a list of function call arguments, *)
  io_trace -> mem -> String.string -> list word ->
  (* and a postcondition on the received memory, function call results, and leakage trace, *)
  (mem -> list word -> list word -> Prop) ->
  (* tells if this postcondition will hold *)
  Prop.

Existing Class ExtSpec.

(*A term of type PickSp is one of the 'oracles' discussed in the paper.
  It takes as argument the leakage-trace-so-far of a program, and it returns the next
  stackalloc address.  (hence the name PickSp, which stands for pick-stack-pointer)*)
Definition PickSp {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} : Type :=
  trace -> word.
Existing Class PickSp.

Module ext_spec.
  Class ok{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte}
    {ext_spec: ExtSpec}: Prop :=
    {
      (* The action name and arguments uniquely determine the footprint of the given-away memory. *)
      unique_mGive_footprint: forall t1 t2 mGive1 mGive2 a args
                                (post1 post2: mem -> list word -> list word -> Prop),
        ext_spec t1 mGive1 a args post1 ->
        ext_spec t2 mGive2 a args post2 ->
        map.same_domain mGive1 mGive2;

      weaken :: forall t mGive act args,
          Morphisms.Proper
            (Morphisms.respectful
               (Morphisms.pointwise_relation Interface.map.rep
                  (Morphisms.pointwise_relation (list word)
                     (Morphisms.pointwise_relation (list word) Basics.impl))) Basics.impl)
            (ext_spec t mGive act args);

      intersect: forall t mGive a args,
        ext_spec t mGive a args (fun mReceive resvals klist =>
                                   forall mid, ext_spec t mGive a args mid ->
                                          mid mReceive resvals klist);
    }.
End ext_spec.
Arguments ext_spec.ok {_ _ _ _} _.

Section binops.
  Context {width : Z} {BW: Bitwidth width} {word : Word.Interface.word width}.
  Definition interp_binop (bop : bopname) : word -> word -> word :=
    match bop with
    | bopname.add => word.add
    | bopname.sub => word.sub
    | bopname.mul => word.mul
    | bopname.mulhuu => word.mulhuu
    | bopname.divu => word.divu
    | bopname.remu => word.modu
    | bopname.and => word.and
    | bopname.or => word.or
    | bopname.xor => word.xor
    | bopname.sru => word.sru
    | bopname.slu => word.slu
    | bopname.srs => word.srs
    | bopname.lts => fun a b =>
                      if word.lts a b then word.of_Z 1 else word.of_Z 0
    | bopname.ltu => fun a b =>
                      if word.ltu a b then word.of_Z 1 else word.of_Z 0
    | bopname.eq => fun a b =>
                     if word.eqb a b then word.of_Z 1 else word.of_Z 0
    end.
  Definition leak_binop (bop : bopname) (x1 : word) (x2 : word) : trace :=
    match bop with
    | bopname.divu | bopname.remu => cons (leak_word x2) (cons (leak_word x1) nil)
    | bopname.sru | bopname.slu | bopname.srs => cons (leak_word x2) nil
    | _ => nil
    end.
End binops.

Section exprs.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).

    Local Notation "' x <- a | y ; f" := (match a with x => f | _ => y end)
                                           (right associativity, at level 70, x pattern).
    Fixpoint eval_expr (e : expr) (tr : trace) : option (word * trace) :=
      match e with
      | expr.literal v => Some (
                             word.of_Z v,
                             tr)
      | expr.var x => match map.get l x with
                     | Some v => Some (
                                    v,
                                    tr)
                     | None => None
                     end
      | expr.inlinetable aSize t index =>
          'Some (index', tr') <- eval_expr index tr | None;
          'Some v <- load aSize (map.of_list_word t) index' | None;
          Some (v,
              leak_word index' :: tr')
      | expr.load aSize a =>
          'Some (a', tr') <- eval_expr a tr | None;
          'Some v <- load aSize m a' | None;
          Some (v,
              leak_word a' :: tr')
      | expr.op op e1 e2 =>
          'Some (v1, tr') <- eval_expr e1 tr | None;
          'Some (v2, tr'') <- eval_expr e2 tr' | None;
          Some (interp_binop op v1 v2,
              leak_binop op v1 v2 ++ tr'')
      | expr.ite c e1 e2 =>
          'Some (vc, tr') <- eval_expr c tr | None;
          eval_expr
            (if word.eqb vc (word.of_Z 0) then e2 else e1)
            ((if word.eqb vc (word.of_Z 0) then leak_bool false else leak_bool true) :: tr')
      end.

    Fixpoint evaluate_call_args_log (arges : list expr) (tr : trace) :=
      match arges with
      | e :: tl =>
          'Some (v, tr') <- eval_expr e tr | None;
          'Some (args, tr'') <- evaluate_call_args_log tl tr' | None;
          Some (v :: args, tr'')
      | _ => Some (nil, tr)
      end.
  End WithMemAndLocals.
End exprs.

Section stmts.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Context (e: env).
  
  Implicit Types post : trace -> io_trace -> mem -> locals -> Prop.
  
  Section WithDet.
    Context (salloc_det : bool).
    Context {pick_sp : PickSp}.

    Inductive exec :
      cmd -> trace -> io_trace -> mem -> locals  ->
      (trace -> io_trace -> mem -> locals -> Prop) -> Prop :=
    | skip
        k t m l post
        (_ : post k t m l)
      : exec cmd.skip k t m l post
    | set x e
        m l post
        k t v k' (_ : eval_expr m l e k = Some (v, k'))
        (_ : post k' t m (map.put l x v))
      : exec (cmd.set x e) k t m l post
    | unset x
        k t m l post
        (_ : post k t m (map.remove l x))
      : exec (cmd.unset x) k t m l post
    | store sz ea ev
        k t m l post
        a k' (_ : eval_expr m l ea k = Some (a, k'))
        v k'' (_ : eval_expr m l ev k' = Some (v, k''))
        m' (_ : store sz m a v = Some m')
        (_ : post (leak_word a :: k'') t m' l)
      : exec (cmd.store sz ea ev) k t m l post
    | stackalloc x n body
        k t mSmall l post
        (_ : Z.modulo n (bytes_per_word width) = 0)
        (_ : forall a mStack mCombined,
            (salloc_det = true -> a = pick_sp k) ->
            anybytes a n mStack ->
            map.split mCombined mSmall mStack ->
            exec body (Leakage.branch a :: k) t mCombined (map.put l x a)
              (fun k' t' mCombined' l' =>
                 exists mSmall' mStack',
                   anybytes a n mStack' /\
                     map.split mCombined' mSmall' mStack' /\
                     post k' t' mSmall' l'))
      : exec (cmd.stackalloc x n body) k t mSmall l post
    | if_true k t m l e c1 c2 post
        v k' (_ : eval_expr m l e k = Some (v, k'))
        (_ : word.unsigned v <> 0)
        (_ : exec c1 (leak_bool true :: k') t m l post)
      : exec (cmd.cond e c1 c2) k t m l post
    | if_false e c1 c2
        k t m l post
        v k' (_ : eval_expr m l e k = Some (v, k'))
        (_ : word.unsigned v = 0)
        (_ : exec c2 (leak_bool false :: k') t m l post)
      : exec (cmd.cond e c1 c2) k t m l post
    | seq c1 c2
        k t m l post
        mid (_ : exec c1 k t m l mid)
        (_ : forall k' t' m' l', mid k' t' m' l' -> exec c2 k' t' m' l' post)
      : exec (cmd.seq c1 c2) k t m l post
    | while_false e c
        k t m l post
        v k' (_ : eval_expr m l e k = Some (v, k'))
        (_ : word.unsigned v = 0)
        (_ : post (leak_bool false :: k') t m l)
      : exec (cmd.while e c) k t m l post
    | while_true e c
        k t m l post
        v k' (_ : eval_expr m l e k = Some (v, k'))
        (_ : word.unsigned v <> 0)
        mid (_ : exec c (leak_bool true :: k') t m l mid)
        (_ : forall k'' t' m' l', mid k'' t' m' l' ->
                                  exec (cmd.while e c) k'' t' m' l' post)
      : exec (cmd.while e c) k t m l post
    | call binds fname arges
        k t m l post
        params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
        args k' (_ : evaluate_call_args_log m l arges k = Some (args, k'))
        lf (_ : map.of_list_zip params args = Some lf)
        mid (_ : exec fbody (leak_unit :: k') t m lf mid)
        (_ : forall k'' t' m' st1, mid k'' t' m' st1 ->
                                   exists retvs, map.getmany_of_list st1 rets = Some retvs /\
                                              exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
                                                      post k'' t' m' l')
      : exec (cmd.call binds fname arges) k t m l post
    | interact binds action arges
        k t m l post
        mKeep mGive (_: map.split m mKeep mGive)
        args k' (_ :  evaluate_call_args_log m l arges k = Some (args, k'))
        mid (_ : ext_spec t mGive action args mid)
        (_ : forall mReceive resvals klist, mid mReceive resvals klist ->
                                       exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
                                               forall m', map.split m' mKeep mReceive ->
                                                     post (leak_list klist :: k')%list (((mGive, action, args), (mReceive, resvals)) :: t) m' l')
      : exec (cmd.interact binds action arges) k t m l post
    .
  End WithDet.

  (*This is the \Downarrow_A predicate of the paper.
    More precisely: for all A, the \Downarrow_A predicate is (exec_det A).*)
  Definition exec_det pick_sp := exec true (pick_sp := pick_sp).

  (*This is the \Downarrow predicate of the paper.
    That is, \Downarrow is exec_nondet.*)
  Definition exec_nondet := exec false (pick_sp := fun _ => word.of_Z 0).
End stmts.
