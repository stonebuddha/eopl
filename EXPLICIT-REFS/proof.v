Require Import Bool ZArith Arith String List Max Logic.Eqdep_dec Program.Equality.
Set Implicit Arguments.

Notation "x <- e1 ; e2" :=
  (match e1 with
   | None => None
   | Some x => e2
   end)
    (right associativity, at level 60).

Hint Resolve eq_nat_dec.
Hint Resolve lt_S_n lt_n_S.

Ltac simplify :=
  repeat
    match goal with
    | [ H1 : False |- _ ] => destruct H1
    | [ |- True ] => constructor
    | [ H1 : True |- _ ] => clear H1
    | [ |- ~ _ ] => intro
    | [ H1 : ~ ?P1, H2 : ?P1 |- _ ] => destruct (H1 H2)
    | [ H1 : _ \/ _ |- _ ] => destruct H1
    | [ |- _ /\ _ ] => constructor
    | [ H1 : _ /\ _ |- _ ] => destruct H1
    | [ H1 : exists _, _ |- _ ] => destruct H1
    | [ |- forall _, _ ] => intro
    | [ _ : ?X1 = ?X2 |- _ ] => subst X2 || subst X1
    end.

Ltac existT_inversion :=
  repeat (
      match goal with
      | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2_eq_dec in H; auto
      end); subst; eauto 10.

Inductive expression : nat -> Set :=
| Const : forall ctx, nat -> expression ctx
| Diff : forall ctx, expression ctx -> expression ctx -> expression ctx
| IsZero : forall ctx, expression ctx -> expression ctx
| If : forall ctx, expression ctx -> expression ctx -> expression ctx -> expression ctx
| Var : forall ctx n, n < ctx -> expression ctx
| Let : forall ctx, expression ctx -> expression (S ctx) -> expression ctx
| Proc : forall ctx, expression (S ctx) -> expression ctx
| Call : forall ctx, expression ctx -> expression ctx -> expression ctx
| Newref : forall ctx, expression ctx -> expression ctx
| Deref : forall ctx, expression ctx -> expression ctx
| Setref : forall ctx, expression ctx -> expression ctx -> expression ctx.

Lemma nltz : forall n, n < O -> False.
  intro; omega.
Qed.

Definition partial_map (ctx : nat) (A : Type) := forall n, n < ctx -> A.
Definition empty {A : Type} : partial_map O A.
  refine (fun _ _ => match nltz _ with end);
    eauto.
Defined.
Definition extend {ctx : nat} {A : Type} (v : A) (m : partial_map ctx A) : partial_map (S ctx) A.
  refine (fun n =>
            match n with
            | O => fun _ => v
            | S n' => fun _ => m _ _
            end);
    eauto.
Defined.

Definition loc := nat.

Inductive expval : Type :=
| Num : Z -> expval
| Bool : bool -> expval
| Clo : forall ctx, expression (S ctx) -> partial_map ctx expval -> expval
| Ref : loc -> expval.

Definition environment ctx := partial_map ctx expval.
Definition empty_env : environment O := empty.
Definition extend_env {ctx : nat} val env : partial_map (S ctx) expval := extend val env.

Definition store := loc -> option expval.
Definition empty_store : store := fun _ => None.
Definition extend_store l val st : store := fun q => if eq_nat_dec q l then Some val else st q.

Lemma extend_store_eq : forall l val st, (extend_store l val st) l = Some val.
  intros.
  unfold extend_store.
  destruct (Nat.eq_dec l l); congruence.
Qed.

Lemma extend_store_neq : forall l q val st, q <> l -> (extend_store l val st) q = st q.
  intros.
  unfold extend_store.
  destruct (Nat.eq_dec q l); congruence.
Qed.

Hint Resolve extend_store_eq extend_store_neq.

Inductive value_of_rel: forall ctx, expression ctx -> environment ctx -> store -> expval -> store -> Prop :=
| VConst :
    forall ctx num env st,
      value_of_rel (Const ctx num) env st (Num (Z.of_nat num)) st
| VDiff :
    forall ctx (exp1 : expression ctx) exp2 num1 num2 env st0 st1 st2,
      value_of_rel exp1 env st0 (Num num1) st1 ->
      value_of_rel exp2 env st1 (Num num2) st2 ->
      value_of_rel (Diff exp1 exp2) env st0 (Num (num1 - num2)) st2
| VIsZero :
    forall ctx (exp1 : expression ctx) num1 env st0 st1,
      value_of_rel exp1 env st0 (Num num1) st1 ->
      value_of_rel (IsZero exp1) env st0 (Bool (Z.eqb num1 0)) st1
| VIfTrue :
    forall ctx (exp1 : expression ctx) exp2 exp3 val2 env st0 st1 st2,
      value_of_rel exp1 env st0 (Bool true) st1 ->
      value_of_rel exp2 env st1 val2 st2 ->
      value_of_rel (If exp1 exp2 exp3) env st0 val2 st2
| VIfFalse :
    forall ctx (exp1 : expression ctx) exp2 exp3 val3 env st0 st1 st2,
      value_of_rel exp1 env st0 (Bool false) st1 ->
      value_of_rel exp3 env st1 val3 st2 ->
      value_of_rel (If exp1 exp2 exp3) env st0 val3 st2
| VVar :
    forall ctx n (pf : n < ctx) env val st,
      env _ pf = val ->
      value_of_rel (Var pf) env st val st
| VLet :
    forall ctx (exp1 : expression ctx) body env val1 val st0 st1 st2,
      value_of_rel exp1 env st0 val1 st1 ->
      value_of_rel body (extend_env val1 env) st1 val st2 ->
      value_of_rel (Let exp1 body) env st0 val st2
| VProc :
    forall ctx (body : expression (S ctx)) env st,
      value_of_rel (Proc body) env st (Clo body env) st
| VCall :
    forall ctx (rator : expression ctx) rand env ctx' (body : expression (S ctx')) saved_env rand_val val st0 st1 st2 st3,
      value_of_rel rator env st0 (Clo body saved_env) st1 ->
      value_of_rel rand env st1 rand_val st2 ->
      value_of_rel body (extend_env rand_val saved_env) st2 val st3 ->
      value_of_rel (Call rator rand) env st0 val st3
| VNewref :
    forall ctx (exp1 : expression ctx) env val1 st0 st1 l,
      value_of_rel exp1 env st0 val1 st1 ->
      st1 l = None ->
      value_of_rel (Newref exp1) env st0 (Ref l) (extend_store l val1 st1)
| VDeref :
    forall ctx (exp1 : expression ctx) env st0 st1 l val,
      value_of_rel exp1 env st0 (Ref l) st1 ->
      st1 l = Some val ->
      value_of_rel (Deref exp1) env st0 val st1
| VSetref :
    forall ctx (exp1 : expression ctx) exp2 env st0 st1 st2 l val2 ori_val,
      value_of_rel exp1 env st0 (Ref l) st1 ->
      value_of_rel exp2 env st1 val2 st2 ->
      st2 l = Some ori_val ->
      value_of_rel (Setref exp1 exp2) env st0 (Num 23%Z) (extend_store l val2 st2).

Lemma value_of_rel_const_inversion :
  forall ctx num env val st0 st1,
    value_of_rel (Const ctx num) env st0 val st1 ->
    val = Num (Z.of_nat num) /\ st0 = st1.
Proof.
  intros.
  inversion H.
  existT_inversion.
Qed.

Lemma value_of_rel_diff_inversion :
  forall ctx (exp1 : expression ctx) exp2 env val st0 st2,
    value_of_rel (Diff exp1 exp2) env st0 val st2 ->
    exists num1 num2 st1,
      value_of_rel exp1 env st0 (Num num1) st1 /\
      value_of_rel exp2 env st1 (Num num2) st2 /\
      val = Num (num1 - num2).
Proof.
  intros.
  inversion H.
  existT_inversion.
Qed.

Lemma value_of_rel_is_zero_inversion :
  forall ctx (exp1 : expression ctx) env val st0 st1,
    value_of_rel (IsZero exp1) env st0 val st1 ->
    exists num1,
      value_of_rel exp1 env st0 (Num num1) st1 /\
      val = Bool (Z.eqb num1 0).
Proof.
  intros.
  inversion H.
  existT_inversion.
Qed.

Lemma value_of_rel_if_inversion :
  forall ctx (exp1 : expression ctx) exp2 exp3 env val st0 st2,
    value_of_rel (If exp1 exp2 exp3) env st0 val st2 ->
    exists st1,
      (value_of_rel exp1 env st0 (Bool true) st1 /\ value_of_rel exp2 env st1 val st2) \/
      (value_of_rel exp1 env st0 (Bool false) st1 /\ value_of_rel exp3 env st1 val st2).
Proof.
  intros.
  inversion H;
    existT_inversion.
Qed.

Lemma value_of_rel_let_inversion :
  forall ctx (exp1 : expression ctx) body env val st0 st2,
    value_of_rel (Let exp1 body) env st0 val st2 ->
    exists val1 st1,
      value_of_rel exp1 env st0 val1 st1 /\
      value_of_rel body (extend_env val1 env) st1 val st2.
Proof.
  intros.
  inversion H.
  existT_inversion.
Qed.

Lemma value_of_rel_var_inversion :
  forall ctx n (pf : n < ctx) env val st0 st1,
    value_of_rel (Var pf) env st0 val st1 ->
    exists (pf : n < ctx),
      env _ pf = val /\ st0 = st1.
Proof.
  intros.
  inversion H.
  existT_inversion.
Qed.

Lemma value_of_rel_proc_inversion :
  forall ctx (body : expression (S ctx)) env val st0 st1,
    value_of_rel (Proc body) env st0 val st1 ->
    val = Clo body env /\ st0 = st1.
Proof.
  intros.
  inversion H.
  existT_inversion.
Qed.

Lemma value_of_rel_call_inversion :
  forall ctx (rator : expression ctx) rand env val st0 st3,
    value_of_rel (Call rator rand) env st0 val st3 ->
    exists ctx' (body : expression (S ctx')) saved_env rand_val st1 st2,
      value_of_rel rator env st0 (Clo body saved_env) st1 /\
      value_of_rel rand env st1 rand_val st2 /\
      value_of_rel body (extend_env rand_val saved_env ) st2 val st3.
Proof.
  intros.
  inversion H.
  existT_inversion.
Qed.

Lemma value_of_rel_newref_inversion :
  forall ctx (exp1 : expression ctx) env val st0 st2,
    value_of_rel (Newref exp1) env st0 val st2 ->
    exists val1 l st1,
      value_of_rel exp1 env st0 val1 st1 /\
      val = Ref l /\ st1 l = None /\
      st2 = extend_store l val1 st1.
Proof.
  intros.
  inversion H.
  existT_inversion.
Qed.

Lemma value_of_rel_deref_inversion :
  forall ctx (exp1 : expression ctx) env val st0 st1,
    value_of_rel (Deref exp1) env st0 val st1 ->
    exists l,
      value_of_rel exp1 env st0 (Ref l) st1 /\
      st1 l = Some val.
Proof.
  intros.
  inversion H.
  existT_inversion.
Qed.

Lemma value_of_rel_setref_inversion :
  forall ctx (exp1 : expression ctx) exp2 env val st0 st3,
    value_of_rel (Setref exp1 exp2) env st0 val st3 ->
    exists val2 l st1 st2 ori_val,
      value_of_rel exp1 env st0 (Ref l) st1 /\
      value_of_rel exp2 env st1 val2 st2 /\
      st2 l = Some ori_val /\
      st3 = extend_store l val2 st2.
Proof.
  intros.
  inversion H.
  existT_inversion.
Qed.

Definition naive_store (sz : nat) := { st : store | forall l, (l < sz -> exists val, st l = Some val) /\ (l >= sz -> st l = None) }.

Definition value_of : forall ctx sz, nat -> expression ctx -> naive_store sz -> environment ctx -> option (expval * { sz : nat & naive_store sz }).
  refine (
      fix F {ctx sz : nat} (fuel : nat) (exp : expression ctx) (st0 : naive_store sz) : environment ctx -> option (expval * { sz : nat & naive_store sz }) :=
        match fuel with
        | O => fun _ => None
        | S fuel' =>
          match exp with
          | Const _ num => fun _ => Some (Num (Z.of_nat num), existT _ _ st0)
          | Diff exp1 exp2 =>
            fun env =>
              ans1 <- F fuel' exp1 st0 env;
              let (val1, ex1) := ans1 in
              match ex1 with
              | existT _ _ st1 =>
                ans2 <- F fuel' exp2 st1 env;
                let (val2, ex2) := ans2 in
                match (val1, val2) with
                | (Num num1, Num num2) => Some (Num (num1 - num2)%Z, ex2)
                | _ => None
                end
              end
          | IsZero exp1 =>
            fun env =>
              ans1 <- F fuel' exp1 st0 env;
              let (val1, ex1) := ans1 in
              match val1 with
              | Num num1 => Some (Bool (Z.eqb num1 0%Z), ex1)
              | _ => None
              end
          | If exp1 exp2 exp3 =>
            fun env =>
              ans1 <- F fuel' exp1 st0 env;
              let (val1, ex1) := ans1 in
              match ex1 with
              | existT _ _ st1 =>
                match val1 with
                | Bool true => F fuel' exp2 st1 env
                | Bool false => F fuel' exp3 st1 env
                | _ => None
                end
              end
          | Var pf => fun env => Some (env _ pf, existT _ _ st0)
          | Let exp1 body =>
            fun env =>
              ans1 <- F fuel' exp1 st0 env;
              let (val1, ex1) := ans1 in
              match ex1 with
              | existT _ _ st1 => F fuel' body st1 (extend_env val1 env)
              end
          | Proc body => fun env => Some (Clo body env, existT _ _ st0)
          | Call rator rand =>
            fun env =>
              ans1 <- F fuel' rator st0 env;
              let (rator_val, ex1) := ans1 in
              match ex1 with
              | existT _ _ st1 =>
                match rator_val with
                | Clo body saved_env =>
                  ans2 <- F fuel' rand st1 env;
                  let (rand_val, ex2) := ans2 in
                  match ex2 with
                  | existT _ _ st2 => F fuel' body st2 (extend_env rand_val saved_env)
                  end
                | _ => None
                end
              end
          | Newref exp1 =>
            fun env =>
              ans1 <- F fuel' exp1 st0 env;
              let (val1, ex1) := ans1 in
              match ex1 with
              | existT _ sz1 st1 =>
                match st1 with
                | exist _ m1 pf1 => Some (Ref sz1, existT _ (S sz1) (exist _ (extend_store sz1 val1 m1) _))
                end
              end
          | Deref exp1 =>
            fun env =>
              ans1 <- F fuel' exp1 st0 env;
              let (val1, ex1) := ans1 in
              match ex1 with
              | existT _ sz1 st1 =>
                match st1 with
                | exist _ m1 _ => 
                  match val1 with
                  | Ref l1 =>
                    match m1 l1 with
                    | Some val => Some (val, ex1)
                    | None => None
                    end
                  | _ => None
                  end
                end
              end
          | Setref exp1 exp2 =>
            fun env =>
              ans1 <- F fuel' exp1 st0 env;
              let (val1, ex1) := ans1 in
              match ex1 with
              | existT _ sz1 st1 =>
                match val1 with
                | Ref l1 =>
                  ans2 <- F fuel' exp2 st1 env;
                  let (val2, ex2) := ans2 in
                  match ex2 with
                  | existT _ sz2 st2 =>
                    if lt_dec l1 sz2 then
                      match st2 with
                      | exist _ m2 pf2 =>
                        Some (Num 23%Z, existT _ sz2 (exist _ (extend_store l1 val2 m2) _))
                      end
                    else
                      None
                  end
                | _ => None
                end
              end
          end
        end).
  intro.
  specialize (pf1 l); simplify.
  assert (l <= sz1). omega.
  destruct H2.
  eauto.
  assert (l < S m). omega.
  rewrite -> extend_store_neq; try omega.
  eauto.
  assert (l >= sz1). omega.
  rewrite -> extend_store_neq; try omega.
  auto.

  intro.
  specialize (pf2 l0); simplify.
  specialize (H H1).
  destruct (Nat.eq_dec l0 l1); simplify.
  rewrite -> extend_store_eq.
  eauto.
  rewrite -> extend_store_neq; auto.
  eauto.
  assert (l0 <> l1). omega.
  rewrite -> extend_store_neq; auto.
Defined.

(*Ltac value_of_equation_finisher :=
  repeat (
      try match goal with
          | [ H : value_of ?FUEL ?EXP ?ENV = _ |- context[match value_of ?FUEL ?EXP ?ENV with Some _ => _ | None => _ end] ] =>
            try (rewrite -> H; clear H)
          | [ H : ?LHS = ?RHS |- context[Some ?LHS = Some ?RHS] ] =>
            rewrite -> H; clear H
          end;
      eauto).

Lemma value_of_diff_equation :
  forall fuel ctx (exp1 : expression ctx) exp2 env num1 num2,
    value_of fuel exp1 env = Some (Num num1) ->
    value_of fuel exp2 env = Some (Num num2) ->
    value_of (S fuel) (Diff exp1 exp2) env = Some (Num (num1 - num2)).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_is_zero_equation :
  forall fuel ctx (exp1 : expression ctx) env num1,
    value_of fuel exp1 env = Some (Num num1) ->
    value_of (S fuel) (IsZero exp1) env = Some (Bool (Z.eqb num1 0)).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_if_true_equation :
  forall fuel ctx (exp1 : expression ctx) exp2 exp3 env val,
    value_of fuel exp1 env = Some (Bool true) ->
    value_of fuel exp2 env = Some val ->
    value_of (S fuel) (If exp1 exp2 exp3) env = Some val.
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_if_false_equation :
  forall fuel ctx (exp1 : expression ctx) exp2 exp3 env val,
    value_of fuel exp1 env = Some (Bool false) ->
    value_of fuel exp3 env = Some val ->
    value_of (S fuel) (If exp1 exp2 exp3) env = Some val.
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_var_equation :
  forall fuel ctx (env : environment ctx) n (pf : n < ctx) val,
    env _ pf = val ->
    value_of (S fuel) (Var pf) env = Some val.
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_let_equation :
  forall fuel ctx (exp1 : expression ctx) body env val1 val,
    value_of fuel exp1 env = Some val1 ->
    value_of fuel body (extend_env val1 env) = Some val ->
    value_of (S fuel) (Let exp1 body) env = Some val.
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_call_equation :
  forall fuel ctx (rator : expression ctx) rand env rand_val val ctx' (body : expression (S ctx')) saved_env,
    value_of fuel rator env = Some (Clo body saved_env) ->
    value_of fuel rand env = Some rand_val ->
    value_of fuel body (extend_env rand_val saved_env) = Some val ->
    value_of (S fuel) (Call rator rand) env = Some val.
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Hint Resolve value_of_diff_equation value_of_is_zero_equation value_of_if_true_equation value_of_if_false_equation value_of_var_equation value_of_let_equation value_of_call_equation.
Hint Constructors value_of_rel.

Theorem value_of_soundness :
  forall ctx (exp : expression ctx) env val,
    (exists fuel, value_of fuel exp env = Some val) ->
    value_of_rel exp env val.
Proof.
  intros.
  destruct 0 as [ fuel ? ].
  generalize dependent ctx.
  generalize dependent val.
  induction fuel; intros; try discriminate; destruct exp;
    match goal with
    | [ H : value_of _ _ _ = _ |- _ ] => simpl in H
    end;
    repeat (
        try match goal with
            | [ _ : context[match value_of ?FUEL ?EXP ?ENV with Some _ => _ | None => _ end] |- _ ] =>
              destruct (value_of FUEL EXP ENV) eqn:?; try discriminate
            | [ _ : context[match ?VAL with Num _ => _ | Bool _ => _ | Clo _ _ => _ end] |- _ ] =>
              destruct VAL; try discriminate
            | [ _ : context[if ?B then _ else _] |- _ ] =>
              destruct B
            | [ H : Some _ = Some _ |- _ ] =>
              inversion H; subst; clear H
            end;
        eauto).
Qed.

Lemma fuel_incr :
  forall fuel ctx (exp : expression ctx) env val,
    value_of fuel exp env = Some val ->
    value_of (S fuel) exp env = Some val.
Proof.
  induction fuel; intros; try discriminate; destruct exp;
    match goal with
    | [ H : value_of _ _ _ = _ |- _ ] => simpl in H
    end;
    repeat (
        try match goal with
            | [ _ : context[match value_of ?FUEL ?EXP ?ENV with Some _ => _ | None => _ end] |- _ ] =>
              destruct (value_of FUEL EXP ENV) eqn:?; try discriminate
            | [ _ : context[match ?VAL with Num _ => _ | Bool _ => _ | Clo _ _ => _ end] |- _ ] =>
              destruct VAL; try discriminate
            | [ _ : context[if ?B then _ else _] |- _ ] =>
              destruct B
            | [ H : Some _ = Some _ |- _ ] =>
              inversion H; subst; clear H
            end;
        eauto).
Qed.

Lemma fuel_order :
  forall ctx (exp : expression ctx) env val fuel fuel',
    value_of fuel exp env = Some val ->
    fuel <= fuel' ->
    value_of fuel' exp env = Some val.
Proof.
  Hint Resolve fuel_incr.
  induction 2; auto.
Qed.

Lemma le_max_1 : forall a b c, a <= max (max a b) c.
  intros.
  rewrite <- max_assoc.
  apply le_max_l.
Qed.

Lemma le_max_2 : forall a b c, b <= max (max a b) c.
  intros.
  rewrite (max_comm a b).
  rewrite <- max_assoc.
  apply le_max_l.
Qed.

Lemma le_max_3 : forall a b c, c <= max (max a b) c.
  intros.
  apply le_max_r.
Qed.

Theorem value_of_completeness :
  forall ctx (exp : expression ctx) env val,
    value_of_rel exp env val ->
    exists fuel, value_of fuel exp env = Some val.
Proof.
  Hint Resolve fuel_order le_max_l le_max_r le_max_1 le_max_2 le_max_3.
  induction 1;
    match goal with
    | [ IH1 : exists _, _, IH2 : exists _, _, IH3 : exists _, _ |- _ ] =>
      destruct IH1 as [ fuel1 ? ]; destruct IH2 as [ fuel2 ? ]; destruct IH3 as [ fuel3 ? ];
        exists (S (max (max fuel1 fuel2) fuel3))
    | [ IH1 : exists _, _, IH2 : exists _, _ |- _ ] =>
      destruct IH1 as [ fuel1 ? ]; destruct IH2 as [ fuel2 ? ];
        exists (S (max fuel1 fuel2))
    | [ IH1 : exists _, _ |- _ ] =>
      destruct IH1 as [ fuel1 ? ];
        exists (S fuel1)
    | [ |- _ ] =>
      exists (S O)
    end;
    eauto.
Qed.

Theorem value_of_correctness :
  forall ctx (exp : expression ctx) env val,
    (exists fuel, value_of fuel exp env = Some val) <->
    value_of_rel exp env val.
Proof.
  Hint Resolve value_of_soundness value_of_completeness.
  intros; split; auto.
Qed.*)