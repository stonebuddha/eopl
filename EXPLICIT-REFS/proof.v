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

Ltac value_of_equation_finisher :=
  repeat (
      try match goal with
          | [ H : value_of ?FUEL ?EXP ?ST ?ENV = _ |- context[match value_of ?FUEL ?EXP ?ST ?ENV with Some _ => _ | None => _ end] ] =>
            try (rewrite -> H; clear H)
          | [ H : ?LHS = ?RHS |- context[Some ?LHS = Some ?RHS] ] =>
            rewrite -> H; clear H
          | [ H : Some _ = Some _ |- _ ] =>
            inversion H; subst; clear H
          end;
      simplify; eauto).

Lemma value_of_const_equation :
  forall fuel ctx num env sz0 (st0 : naive_store sz0),
    value_of (S fuel) (Const ctx num) st0 env = Some (Num (Z.of_nat num), existT _ _ st0).
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_diff_equation :
  forall fuel ctx (exp1 : expression ctx) exp2 env num1 num2 sz0 (st0 : naive_store sz0) sz1 st1 sz2 st2,
    value_of fuel exp1 st0 env = Some (Num num1, existT _ sz1 st1) ->
    value_of fuel exp2 st1 env = Some (Num num2, existT _ sz2 st2) ->
    value_of (S fuel) (Diff exp1 exp2) st0 env = Some (Num (num1 - num2), existT _ _ st2).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_is_zero_equation :
  forall fuel ctx (exp1 : expression ctx) env num1 sz0 (st0 : naive_store sz0) sz1 st1,
    value_of fuel exp1 st0 env = Some (Num num1, existT _ sz1 st1) ->
    value_of (S fuel) (IsZero exp1) st0 env = Some (Bool (Z.eqb num1 0), existT _ _ st1).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_if_true_equation :
  forall fuel ctx (exp1 : expression ctx) exp2 exp3 env val sz0 (st0 : naive_store sz0) sz1 st1 sz2 st2,
    value_of fuel exp1 st0 env = Some (Bool true, existT _ sz1 st1) ->
    value_of fuel exp2 st1 env = Some (val, existT _ sz2 st2) ->
    value_of (S fuel) (If exp1 exp2 exp3) st0 env = Some (val, existT _ _ st2).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_if_false_equation :
  forall fuel ctx (exp1 : expression ctx) exp2 exp3 env val sz0 (st0 : naive_store sz0) sz1 st1 sz2 st2,
    value_of fuel exp1 st0 env = Some (Bool false, existT _ sz1 st1) ->
    value_of fuel exp3 st1 env = Some (val, existT _ sz2 st2) ->
    value_of (S fuel) (If exp1 exp2 exp3) st0 env = Some (val, existT _ _ st2).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_var_equation :
  forall fuel ctx (env : environment ctx) n (pf : n < ctx) val sz0 (st0 : naive_store sz0),
    env _ pf = val ->
    value_of (S fuel) (Var pf) st0 env = Some (val, existT _ _ st0).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_let_equation :
  forall fuel ctx (exp1 : expression ctx) body env val1 val sz0 (st0 : naive_store sz0) sz1 st1 sz2 st2,
    value_of fuel exp1 st0 env = Some (val1, existT _ sz1 st1) ->
    value_of fuel body st1 (extend_env val1 env) = Some (val, existT _ sz2 st2) ->
    value_of (S fuel) (Let exp1 body) st0 env = Some (val, existT _ _ st2).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_proc_equation :
  forall fuel ctx (body : expression (S ctx)) (env : environment ctx) sz0 (st0 : naive_store sz0) env,
    value_of (S fuel) (Proc body) st0 env = Some (Clo body env, existT _ _ st0).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_call_equation :
  forall fuel ctx (rator : expression ctx) rand env rand_val val ctx' (body : expression (S ctx')) saved_env sz0 (st0 : naive_store sz0) sz1 st1 sz2 st2 sz3 st3,
    value_of fuel rator st0 env = Some (Clo body saved_env, existT _ sz1 st1) ->
    value_of fuel rand st1 env = Some (rand_val, existT _ sz2 st2) ->
    value_of fuel body st2 (extend_env rand_val saved_env) = Some (val, existT _ sz3 st3) ->
    value_of (S fuel) (Call rator rand) st0 env = Some (val, existT _ _ st3).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_newref_equation :
  forall fuel ctx (exp1 : expression ctx) env val1 sz0 (st0 : naive_store sz0) sz1 m1 pf1,
    value_of fuel exp1 st0 env = Some (val1, existT _ sz1 (exist _ m1 pf1)) ->
    exists pf1,
      value_of (S fuel) (Newref exp1) st0 env = Some (Ref sz1, existT _ (S sz1) (exist _ (extend_store sz1 val1 m1) pf1)).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
Qed.

Lemma value_of_deref_equation :
  forall fuel ctx (exp1 : expression ctx) env l1 sz0 (st0 : naive_store sz0) val sz1 m1 pf1,
    value_of fuel exp1 st0 env = Some (Ref l1, existT _ sz1 (exist _ m1 pf1)) ->
    m1 l1 = Some val ->
    value_of (S fuel) (Deref exp1) st0 env = Some (val, existT _ _ (exist _ m1 pf1)).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
  destruct (m1 l1); try discriminate.
  value_of_equation_finisher.
Qed.

Lemma value_of_setref_equation :
  forall fuel ctx (exp1 : expression ctx) exp2 env l1 val2 sz0 (st0 : naive_store sz0) sz1 st1 sz2 m2 pf2,
    value_of fuel exp1 st0 env = Some (Ref l1, existT _ sz1 st1) ->
    value_of fuel exp2 st1 env = Some (val2, existT _ sz2 (exist _ m2 pf2)) ->
    l1 < sz2 ->
    exists pf2,
      value_of (S fuel) (Setref exp1 exp2) st0 env = Some (Num 23, existT _ sz2 (exist _ (extend_store l1 val2 m2) pf2)).
Proof.
  intros.
  simpl.
  value_of_equation_finisher.
  destruct (lt_dec l1 sz2); try congruence.
  value_of_equation_finisher.
Qed.

Hint Resolve value_of_const_equation value_of_diff_equation value_of_is_zero_equation value_of_if_true_equation value_of_if_false_equation value_of_var_equation value_of_let_equation value_of_proc_equation value_of_call_equation value_of_newref_equation value_of_deref_equation value_of_setref_equation.
Hint Constructors value_of_rel.

Theorem value_of_soundness :
  forall ctx (exp : expression ctx) env val sz0 (st0 : naive_store sz0) m0 pf0 sz1 m1 pf1,
    (exists fuel, value_of fuel exp st0 env = Some (val, existT _ sz1 (exist _ m1 pf1))) ->
    st0 = exist _ m0 pf0 ->
    value_of_rel exp env m0 val m1.
Proof.
  intros.
  destruct H as [ fuel ? ].
  generalize dependent ctx.
  generalize dependent val.
  generalize dependent sz0.
  generalize dependent sz1.
  generalize dependent m0.
  generalize dependent m1.
  induction fuel; try discriminate.
  intros.
  dependent destruction exp;
  match goal with
  | [ H : value_of ?FUEL ?EXP ?ST ?ENV = _ |- _ ] => simpl in H
  end;
  repeat (
      try match goal with
          | [ _ : context[match value_of ?FUEL ?EXP ?ST ?ENV with Some _ => _ | None => _ end] |- _ ] => destruct (value_of FUEL EXP ST ENV) eqn:?; try discriminate
          | [ _ : context[let (_, _) := ?X in _] |- _ ] => destruct X
          | [ _ : context[match ?VAL with Num _ => _ | Bool _ => _ | Clo _ _ => _ | Ref _ => _ end] |- _ ] => destruct VAL; try discriminate
          | [ _ : context[if ?B then _ else _] |- _ ] => destruct B
          | [ _ : context[match ?ST ?LOC with Some _ => _ | None => _ end] |- _ ] => destruct (ST LOC) eqn:?; try discriminate
          | [ _ : context[match lt_dec ?X ?Y with left _ => _ | right _ => _ end] |- _ ] => destruct (lt_dec X Y); try discriminate
          | [ st : naive_store _ |- _ ] => destruct st
          | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
          | [ H : exist _ _ _ = exist _ _ _ |- _ ] => inversion H; clear H
          | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H
          end;
      simplify;
      eauto 10).

  assert (pf := a).
  specialize (pf x).
  simplify.
  eauto.

  assert (pf := a).
  specialize (pf l).
  simplify.
  apply H in l0.
  simplify.
  eauto.
Qed.

Lemma fuel_incr :
  forall fuel ctx (exp : expression ctx) env val sz0 m0 (pf0 : forall l, (l < sz0 -> exists val, m0 l = Some val) /\ (l >= sz0 -> m0 l = None)) sz1 m1 pf1,
    value_of fuel exp (exist _ m0 pf0) env = Some (val, existT _ sz1 (exist _ m1 pf1)) ->
    forall pf0, exists pf1,
      value_of (S fuel) exp (exist (fun st => forall l, (l < sz0 -> exists val, st l = Some val) /\ (l >= sz0 -> st l = None)) m0 pf0) env = Some (val, existT _ sz1 (exist _ m1 pf1)).
Proof.
  intros.
  generalize dependent ctx.
  generalize dependent val.
  generalize dependent sz0.
  generalize dependent sz1.
  generalize dependent m1.
  generalize dependent m0.
  induction fuel; try discriminate.
  intros.
  dependent destruction exp;
  match goal with
  | [ H : value_of ?FUEL ?EXP ?ST ?ENV = _ |- _ ] => simpl in H
  end;
  repeat (
      try match goal with
          | [ _ : context[match value_of ?FUEL ?EXP ?ST ?ENV with Some _ => _ | None => _ end] |- _ ] => destruct (value_of FUEL EXP ST ENV) eqn:?; try discriminate
          | [ _ : context[let (_, _) := ?X in _] |- _ ] => destruct X
          | [ _ : context[match ?VAL with Num _ => _ | Bool _ => _ | Clo _ _ => _ | Ref _ => _ end] |- _ ] => destruct VAL; try discriminate
          | [ _ : context[if ?B then _ else _] |- _ ] => destruct B
          | [ _ : context[match ?ST ?LOC with Some _ => _ | None => _ end] |- _ ] => destruct (ST LOC) eqn:?; try discriminate
          | [ _ : context[match lt_dec ?X ?Y with left _ => _ | right _ => _ end] |- _ ] => destruct (lt_dec X Y); try discriminate
          | [ st : naive_store _ |- _ ] => destruct st
          | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
          end;
      simplify;
      eauto 10).

  apply IHfuel with (pf2 := pf2) in Heqo; auto; simplify.
  apply IHfuel with (pf2 := x1) in Heqo0; auto; simplify.
  eauto.

  apply IHfuel with (pf2 := pf2) in Heqo; auto; simplify.
  eauto.

  apply IHfuel with (pf2 := pf2) in Heqo; auto; simplify.
  apply IHfuel with (pf2 := x1) in H; auto; simplify.
  eauto.

  apply IHfuel with (pf2 := pf2) in Heqo; auto; simplify.
  apply IHfuel with (pf2 := x1) in H; auto; simplify.
  eauto.

  apply IHfuel with (pf2 := pf2) in Heqo; auto; simplify.
  apply IHfuel with (pf2 := x1) in H; auto; simplify.
  eauto.

  apply IHfuel with (pf2 := pf2) in Heqo; auto; simplify.
  apply IHfuel with (pf2 := x3) in Heqo0; auto; simplify.
  apply IHfuel with (pf2 := x4) in H; auto; simplify.
  eauto.

  apply IHfuel with (pf2 := pf2) in Heqo; auto; simplify.
  eauto.

  apply IHfuel with (pf2 := pf2) in Heqo; auto; simplify.
  eauto.

  apply IHfuel with (pf2 := pf2) in Heqo; auto; simplify.
  apply IHfuel with (pf2 := x3) in Heqo0; auto; simplify.
  eauto.
Qed.

Lemma fuel_order :
  forall ctx (exp : expression ctx) env val fuel fuel' sz0 m0 (pf0 : forall l, (l < sz0 -> exists val, m0 l = Some val) /\ (l >= sz0 -> m0 l = None)) sz1 m1 pf1,
    value_of fuel exp (exist _ m0 pf0) env = Some (val, existT _ sz1 (exist _ m1 pf1)) ->
    fuel <= fuel' ->
    exists pf1,
    value_of fuel' exp (exist (fun st => forall l, (l < sz0 -> exists val, st l = Some val) /\ (l >= sz0 -> st l = None)) m0 pf0) env = Some (val, existT _ sz1 (exist _ m1 pf1)).
Proof.
  Hint Resolve fuel_incr.
  intros.
  generalize dependent ctx.
  generalize dependent val.
  generalize dependent sz0.
  generalize dependent m0.
  generalize dependent sz1.
  generalize dependent m1.
  induction H0; intros.
  eauto.
  apply IHle in H; simplify; eauto.
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
  forall ctx (exp : expression ctx) env val sz0 (st0 : naive_store sz0) sz1 st1 m0 m1 pf0 pf1,
    value_of_rel exp env m0 val m1 ->
    st0 = exist _ m0 pf0 ->
    st1 = exist _ m1 pf1 ->
    exists fuel, value_of fuel exp st0 env = Some (val, existT _ sz1 st1).
Proof.
  Hint Resolve fuel_order le_max_l le_max_r le_max_1 le_max_2 le_max_3.
Admitted.

Theorem value_of_correctness :
  forall ctx (exp : expression ctx) env val sz0 (st0 : naive_store sz0) sz1 st1 m0 m1 pf0 pf1,
    st0 = exist _ m0 pf0 ->
    st1 = exist _ m1 pf1 ->
    (exists fuel, value_of fuel exp st0 env = Some (val, existT _ sz1 st1)) <->
    value_of_rel exp env m0 val m1.
Proof.
  Hint Resolve value_of_soundness value_of_completeness.
  intros; split; simplify; eauto.
Qed.