Require Import Bool ZArith Arith String List Max Logic.Eqdep_dec Program.Equality.
Set Implicit Arguments.

Notation "x <- e1 ; e2" :=
  (match e1 with
   | None => None
   | Some x => e2
   end)
    (right associativity, at level 60).

Hint Resolve eq_nat_dec.

Ltac simplify :=
  repeat
    match goal with
    | h1 : False |- _ => destruct h1
    | |- True => constructor
    | h1 : True |- _ => clear h1
    | |- ~ _ => intro
    | h1 : ~ ?p1, h2 : ?p1 |- _ => destruct (h1 h2)
    | h1 : _ \/ _ |- _ => destruct h1
    | |- _ /\ _ => constructor
    | h1 : _ /\ _ |- _ => destruct h1
    | h1 : exists _, _ |- _ => destruct h1
    | |- forall _, _ => intro
    | _ : ?x1 = ?x2 |- _ => subst x2 || subst x1
    end.

Ltac existT_inversion :=
  repeat (
      match goal with
      | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2_eq_dec in H; auto
      end); subst; eauto 10.

Module Proc.
  Inductive expression : Set :=
  | Const : nat -> expression
  | Diff : expression -> expression -> expression
  | IsZero : expression -> expression
  | If : expression -> expression -> expression -> expression
  | Var : string -> expression
  | Let : string -> expression -> expression -> expression
  | Proc : string -> expression -> expression
  | Call : expression -> expression -> expression.

  Inductive expval : Set :=
  | Num : Z -> expval
  | Bool : bool -> expval
  | Clo : string -> expression -> environment -> expval

  with

  environment : Set :=
  | Empty : environment
  | Extend : string -> expval -> environment -> environment.

  Fixpoint assoc_error (x : string) (env : environment) : option expval :=
    match env with
    | Empty => None
    | Extend y val saved_env => if string_dec x y then Some val else assoc_error x saved_env
    end.

  Inductive value_of_rel : expression -> environment -> expval -> Prop :=
  | VConst :
      forall num env,
        value_of_rel (Const num) env (Num (Z.of_nat num))
  | VDiff :
      forall exp1 exp2 num1 num2 env,
        value_of_rel exp1 env (Num num1) ->
        value_of_rel exp2 env (Num num2) ->
        value_of_rel (Diff exp1 exp2) env (Num (num1 - num2))
  | VIsZero :
      forall exp1 num1 env,
        value_of_rel exp1 env (Num num1) ->
        value_of_rel (IsZero exp1) env (Bool (Z.eqb num1 0))
  | VIfTrue :
      forall exp1 exp2 exp3 val2 env,
        value_of_rel exp1 env (Bool true) ->
        value_of_rel exp2 env val2 ->
        value_of_rel (If exp1 exp2 exp3) env val2
  | VIfFalse :
      forall exp1 exp2 exp3 val3 env,
        value_of_rel exp1 env (Bool false) ->
        value_of_rel exp3 env val3 ->
        value_of_rel (If exp1 exp2 exp3) env val3
  | VVar :
      forall var env val,
        assoc_error var env = Some val ->
        value_of_rel (Var var) env val
  | VLet :
      forall var exp1 body env val1 valb,
        value_of_rel exp1 env val1 ->
        value_of_rel body (Extend var val1 env) valb ->
        value_of_rel (Let var exp1 body) env valb
  | VProc :
      forall var body env,
        value_of_rel (Proc var body) env (Clo var body env)
  | VCall :
      forall rator rand env var body saved_env rand_val valb,
        value_of_rel rator env (Clo var body saved_env) ->
        value_of_rel rand env rand_val ->
        value_of_rel body (Extend var rand_val saved_env) valb ->
        value_of_rel (Call rator rand) env valb.
End Proc.

Module Lexical.
  Inductive expression : nat -> Set :=
  | Const : forall ctx, nat -> expression ctx
  | Diff : forall ctx, expression ctx -> expression ctx -> expression ctx
  | IsZero : forall ctx, expression ctx -> expression ctx
  | If : forall ctx, expression ctx -> expression ctx -> expression ctx -> expression ctx
  | Var : forall ctx n, n < ctx -> expression ctx
  | Let : forall ctx, expression ctx -> expression (S ctx) -> expression ctx
  | Proc : forall ctx, expression (S ctx) -> expression ctx
  | Call : forall ctx, expression ctx -> expression ctx -> expression ctx.

  Inductive expval : Set :=
  | Num : Z -> expval
  | Bool : bool -> expval
  | Clo : forall ctx, expression (S ctx) -> environment ctx -> expval

  with

  environment : nat -> Set :=
  | Empty : environment O
  | Extend : forall ctx, expval -> environment ctx -> environment (S ctx).

  Lemma nltz : forall n, n < O -> False.
    intro; omega.
  Qed.

  Fixpoint nth {ctx : nat} (n : nat) (env : environment ctx) : n < ctx -> expval :=
    match env in (environment ctx) with
    | Empty => fun pf => match nltz pf with end
    | Extend val saved_env =>
      match n with
      | O => fun _ => val
      | S _ => fun pf => nth saved_env (lt_S_n _ _ pf)
      end
    end.

  Inductive value_of_rel: forall ctx, expression ctx -> environment ctx -> expval -> Prop :=
  | VConst :
      forall ctx num env,
        value_of_rel (Const ctx num) env (Num (Z.of_nat num))
  | VDiff :
      forall ctx (exp1 : expression ctx) exp2 num1 num2 env,
        value_of_rel exp1 env (Num num1) ->
        value_of_rel exp2 env (Num num2) ->
        value_of_rel (Diff exp1 exp2) env (Num (num1 - num2))
  | VIsZero :
      forall ctx (exp1 : expression ctx) num1 env,
        value_of_rel exp1 env (Num num1) ->
        value_of_rel (IsZero exp1) env (Bool (Z.eqb num1 0))
  | VIfTrue :
      forall ctx (exp1 : expression ctx) exp2 exp3 val2 env,
        value_of_rel exp1 env (Bool true) ->
        value_of_rel exp2 env val2 ->
        value_of_rel (If exp1 exp2 exp3) env val2
  | VIfFalse :
      forall ctx (exp1 : expression ctx) exp2 exp3 val3 env,
        value_of_rel exp1 env (Bool false) ->
        value_of_rel exp3 env val3 ->
        value_of_rel (If exp1 exp2 exp3) env val3
  | VVar :
      forall ctx n (pf : n < ctx) env val,
        nth env pf = val ->
        value_of_rel (Var pf) env val
  | VLet :
      forall ctx (exp1 : expression ctx) body env val1 val,
        value_of_rel exp1 env val1 ->
        value_of_rel body (Extend val1 env) val ->
        value_of_rel (Let exp1 body) env val
  | VProc :
      forall ctx (body : expression (S ctx)) env,
        value_of_rel (Proc body) env (Clo body env)
  | VCall :
      forall ctx (rator : expression ctx) rand env ctx' (body : expression (S ctx')) saved_env rand_val val,
        value_of_rel rator env (Clo body saved_env) ->
        value_of_rel rand env rand_val ->
        value_of_rel body (Extend rand_val saved_env) val ->
        value_of_rel (Call rator rand) env val.

  Lemma value_of_rel_const_inversion :
    forall ctx num env val,
      value_of_rel (Const ctx num) env val ->
      val = Num (Z.of_nat num).
  Proof.
    intros.
    inversion H.
    existT_inversion.
  Qed.

  Lemma value_of_rel_diff_inversion :
    forall ctx (exp1 : expression ctx) exp2 env val,
      value_of_rel (Diff exp1 exp2) env val ->
      exists num1 num2,
        value_of_rel exp1 env (Num num1) /\
        value_of_rel exp2 env (Num num2) /\
        val = Num (num1 - num2).
  Proof.
    intros.
    inversion H.
    existT_inversion.
  Qed.

  Lemma value_of_rel_is_zero_inversion :
    forall ctx (exp1 : expression ctx) env val,
      value_of_rel (IsZero exp1) env val ->
      exists num1,
        value_of_rel exp1 env (Num num1) /\
        val = Bool (Z.eqb num1 0).
  Proof.
    intros.
    inversion H.
    existT_inversion.
  Qed.

  Lemma value_of_rel_if_inversion :
    forall ctx (exp1 : expression ctx) exp2 exp3 env val,
      value_of_rel (If exp1 exp2 exp3) env val ->
      (value_of_rel exp1 env (Bool true) /\ value_of_rel exp2 env val) \/
      (value_of_rel exp1 env (Bool false) /\ value_of_rel exp3 env val).
  Proof.
    intros.
    inversion H;
      existT_inversion.
  Qed.

  Lemma value_of_rel_let_inversion :
    forall ctx (exp1 : expression ctx) body env val,
      value_of_rel (Let exp1 body) env val ->
      exists val1,
        value_of_rel exp1 env val1 /\
        value_of_rel body (Extend val1 env) val.
  Proof.
    intros.
    inversion H.
    existT_inversion.
  Qed.

  Lemma value_of_rel_var_inversion :
    forall ctx n (pf : n < ctx) env val,
      value_of_rel (Var pf) env val ->
      exists (pf : n < ctx), nth env pf = val.
  Proof.
    intros.
    inversion H.
    existT_inversion.
  Qed.

  Lemma value_of_rel_proc_inversion :
    forall ctx (body : expression (S ctx)) env val,
      value_of_rel (Proc body) env val ->
      val = Clo body env.
  Proof.
    intros.
    inversion H.
    existT_inversion.
  Qed.

  Lemma value_of_rel_call_inversion :
    forall ctx (rator : expression ctx) rand env val,
      value_of_rel (Call rator rand) env val ->
      exists ctx' (body : expression (S ctx')) saved_env rand_val,
        value_of_rel rator env (Clo body saved_env) /\
        value_of_rel rand env rand_val /\
        value_of_rel body (Extend rand_val saved_env ) val.
  Proof.
    intros.
    inversion H.
    existT_inversion.
  Qed.

  Fixpoint value_of {ctx : nat} (fuel : nat) (exp : expression ctx) : environment ctx -> option expval :=
    match fuel with
    | O => fun _ => None
    | S fuel' =>
      match exp with
      | Const _ num => fun _ => Some (Num (Z.of_nat num))
      | Diff exp1 exp2 => fun env =>
                             val1 <- value_of fuel' exp1 env;
                               val2 <- value_of fuel' exp2 env;
                               match (val1, val2) with
                               | (Num num1, Num num2) => Some (Num (num1 - num2))
                               | _ => None
                               end
      | IsZero exp1 => fun env =>
                          val1 <- value_of fuel' exp1 env;
                            match val1 with
                            | Num num1 => Some (Bool (Z.eqb num1 0))
                            | _ => None
                            end
      | If exp1 exp2 exp3 => fun env =>
                                val1 <- value_of fuel' exp1 env;
                                  match val1 with
                                  | Bool true => value_of fuel' exp2 env
                                  | Bool false => value_of fuel' exp3 env
                                  | _ => None
                                  end
      | Var pf => fun env => Some (nth env pf)
      | Let exp1 body => fun env =>
                            val1 <- value_of fuel' exp1 env;
                              value_of fuel' body (Extend val1 env)
      | Proc body => fun env => Some (Clo body env)
      | Call rator rand => fun env =>
                              rator_val <- value_of fuel' rator env;
                                match rator_val with
                                | Clo body saved_env =>
                                  rand_val <- value_of fuel' rand env;
                                    value_of fuel' body (Extend rand_val saved_env)
                                | _ => None
                                end
      end
    end.

  Lemma value_of_diff_equation :
    forall fuel ctx (exp1 : expression ctx) exp2 env num1 num2,
      value_of fuel exp1 env = Some (Num num1) ->
      value_of fuel exp2 env = Some (Num num2) ->
      value_of (S fuel) (Diff exp1 exp2) env = Some (Num (num1 - num2)).
  Proof.
    intros.
    simpl.
    rewrite -> H.
    rewrite -> H0.
    trivial.
  Qed.

  Lemma value_of_is_zero_equation :
    forall fuel ctx (exp1 : expression ctx) env num1,
      value_of fuel exp1 env = Some (Num num1) ->
      value_of (S fuel) (IsZero exp1) env = Some (Bool (Z.eqb num1 0)).
  Proof.
    intros.
    simpl.
    rewrite -> H.
    trivial.
  Qed.

  Lemma value_of_if_true_equation :
    forall fuel ctx (exp1 : expression ctx) exp2 exp3 env val,
      value_of fuel exp1 env = Some (Bool true) ->
      value_of fuel exp2 env = Some val ->
      value_of (S fuel) (If exp1 exp2 exp3) env = Some val.
  Proof.
    intros.
    simpl.
    rewrite -> H.
    trivial.
  Qed.

  Lemma value_of_if_false_equation :
    forall fuel ctx (exp1 : expression ctx) exp2 exp3 env val,
      value_of fuel exp1 env = Some (Bool false) ->
      value_of fuel exp3 env = Some val ->
      value_of (S fuel) (If exp1 exp2 exp3) env = Some val.
  Proof.
    intros.
    simpl.
    rewrite -> H.
    trivial.
  Qed.

  Lemma value_of_var_equation :
    forall fuel ctx (env : environment ctx) n (pf : n < ctx) val,
      nth env pf = val ->
      value_of (S fuel) (Var pf) env = Some val.
  Proof.
    intros.
    simpl.
    rewrite -> H.
    trivial.
  Qed.

  Lemma value_of_let_equation :
    forall fuel ctx (exp1 : expression ctx) body env val1 val,
      value_of fuel exp1 env = Some val1 ->
      value_of fuel body (Extend val1 env) = Some val ->
      value_of (S fuel) (Let exp1 body) env = Some val.
  Proof.
    intros.
    simpl.
    rewrite -> H.
    trivial.
  Qed.

  Lemma value_of_call_equation :
    forall fuel ctx (rator : expression ctx) rand env rand_val val ctx' (body : expression (S ctx')) saved_env,
      value_of fuel rator env = Some (Clo body saved_env) ->
      value_of fuel rand env = Some rand_val ->
      value_of fuel body (Extend rand_val saved_env) = Some val ->
      value_of (S fuel) (Call rator rand) env = Some val.
  Proof.
    intros.
    simpl.
    rewrite -> H.
    rewrite -> H0.
    trivial.
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
  Qed.
End Lexical.

Module Translation.
  Inductive static_environment : nat -> Set :=
  | Empty : static_environment O
  | Extend : forall ctx, string -> static_environment ctx -> static_environment (S ctx).

  Fixpoint find_index {ctx : nat} (x : string) (senv : static_environment ctx) : option { n : nat | n < ctx } :=
    match senv with
    | Empty => None
    | Extend y saved_senv =>
      if string_dec x y then
        Some (exist _ O (lt_0_Sn _))
      else
        res <- find_index x saved_senv;
        match res with
        | exist _ n pf => Some (exist _ (S n) (lt_n_S _ _ pf))
        end
    end.

  Function translation_of {ctx : nat} (exp : Proc.expression) (senv : static_environment ctx) : option (Lexical.expression ctx) :=
    match exp with
    | Proc.Const num => Some (Lexical.Const _ num)
    | Proc.Diff exp1 exp2 =>
      exp1 <- translation_of exp1 senv;
        exp2 <- translation_of exp2 senv;
        Some (Lexical.Diff exp1 exp2)
    | Proc.IsZero exp1 =>
      exp1 <- translation_of exp1 senv;
        Some (Lexical.IsZero exp1)
    | Proc.If exp1 exp2 exp3 =>
      exp1 <- translation_of exp1 senv;
        exp2 <- translation_of exp2 senv;
        exp3 <- translation_of exp3 senv;
        Some (Lexical.If exp1 exp2 exp3)
    | Proc.Var var =>
      res <- find_index var senv;
        match res with
        | exist _ _ pf => Some (Lexical.Var pf)
        end
    | Proc.Let var exp1 body =>
      exp1 <- translation_of exp1 senv;
        body <- translation_of body (Extend var senv);
        Some (Lexical.Let exp1 body)
    | Proc.Proc var body =>
      body <- translation_of body (Extend var senv);
        Some (Lexical.Proc body)
    | Proc.Call rator rand =>
      rator <- translation_of rator senv;
        rand <- translation_of rand senv;
        Some (Lexical.Call rator rand)
    end.

  Ltac translation_of_inversion_finisher :=
    repeat (
        try match goal with
            | [ _ : context[match translation_of ?EXP ?SENV with Some _ => _ | None => _ end] |- _ ] =>
              destruct (translation_of EXP SENV) eqn:?; try discriminate
            | [ _ : context[match find_index ?S ?SENV with Some _ => _ | None => _ end] |- _ ] =>
              destruct (find_index S SENV) eqn:?; try discriminate
            | [ _ : context[let (_, _) := ?BIND in _] |- _ ] =>
              destruct BIND
            | [ H : Some _ = Some _ |- _ ] =>
              inversion H; subst; clear H
            | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
              apply inj_pair2_eq_dec in H; try apply eq_nat_dec; subst
            end;
        eauto 10).

  Lemma translation_of_const_inversion :
    forall ctx exp (senv : static_environment ctx) num,
      translation_of exp senv = Some (Lexical.Const _ num) ->
      exp = Proc.Const num.
  Proof.
    intros.
    rewrite translation_of_equation in H.
    destruct exp;
      translation_of_inversion_finisher.
  Qed.

  Lemma translation_of_diff_inversion :
    forall ctx exp (senv : static_environment ctx) exp1' exp2',
      translation_of exp senv = Some (Lexical.Diff exp1' exp2') ->
      exists exp1 exp2,
        exp = Proc.Diff exp1 exp2 /\
        translation_of exp1 senv = Some exp1' /\
        translation_of exp2 senv = Some exp2'.
  Proof.
    intros.
    rewrite translation_of_equation in H.
    destruct exp;
      translation_of_inversion_finisher.
  Qed.

  Lemma translation_of_is_zero_inversion :
    forall ctx exp (senv : static_environment ctx) exp1',
      translation_of exp senv = Some (Lexical.IsZero exp1') ->
      exists exp1,
        exp = Proc.IsZero exp1 /\
        translation_of exp1 senv = Some exp1'.
  Proof.
    intros.
    rewrite translation_of_equation in H.
    destruct exp;
      translation_of_inversion_finisher.
  Qed.

  Lemma translation_of_if_inversion :
    forall ctx exp (senv : static_environment ctx) exp1' exp2' exp3',
      translation_of exp senv = Some (Lexical.If exp1' exp2' exp3') ->
      exists exp1 exp2 exp3,
        exp = Proc.If exp1 exp2 exp3 /\
        translation_of exp1 senv = Some exp1' /\
        translation_of exp2 senv = Some exp2' /\
        translation_of exp3 senv = Some exp3'.
  Proof.
    intros.
    rewrite translation_of_equation in H.
    destruct exp;
      translation_of_inversion_finisher.
  Qed.

  Lemma translation_of_var_inversion :
    forall ctx exp (senv : static_environment ctx) n (pf : n < ctx),
      translation_of exp senv = Some (Lexical.Var pf) ->
      exists var (pf' : n < ctx),
        exp = Proc.Var var /\
        find_index var senv = Some (exist _ n pf').
  Proof.
    intros.
    rewrite translation_of_equation in H.
    destruct exp;
      translation_of_inversion_finisher.
  Qed.

  Lemma translation_of_let_inversion :
    forall ctx exp (senv : static_environment ctx) exp1' body',
      translation_of exp senv = Some (Lexical.Let exp1' body') ->
      exists var exp1 body,
        exp = Proc.Let var exp1 body /\
        translation_of exp1 senv = Some exp1' /\
        translation_of body (Extend var senv) = Some body'.
  Proof.
    intros.
    rewrite translation_of_equation in H.
    destruct exp;
      translation_of_inversion_finisher.
  Qed.

  Lemma translation_of_proc_inversion :
    forall ctx exp (senv : static_environment ctx) body',
      translation_of exp senv = Some (Lexical.Proc body') ->
      exists var body,
        exp = Proc.Proc var body /\
        translation_of body (Extend var senv) = Some body'.
  Proof.
    intros.
    rewrite translation_of_equation in H.
    destruct exp;
      translation_of_inversion_finisher.
  Qed.

  Lemma translation_of_call_inversion :
    forall ctx exp (senv : static_environment ctx) rator' rand',
      translation_of exp senv = Some (Lexical.Call rator' rand') ->
      exists rator rand,
        exp = Proc.Call rator rand /\
        translation_of rator senv = Some rator' /\
        translation_of rand senv = Some rand'.
  Proof.
    intros.
    rewrite translation_of_equation in H.
    destruct exp;
      translation_of_inversion_finisher.
  Qed.

  Inductive proc_env_static_env_rel : forall ctx, Proc.environment -> static_environment ctx -> Prop :=
  | PSEmpty : proc_env_static_env_rel (Proc.Empty) Empty
  | PSExtend :
      forall ctx x val saved_env (saved_senv : static_environment ctx),
        proc_env_static_env_rel saved_env saved_senv ->
        proc_env_static_env_rel (Proc.Extend x val saved_env) (Extend x saved_senv).

  Inductive proc_env_lexical_env_rel : forall ctx, Proc.environment -> Lexical.environment ctx -> Prop :=
  | PLEmpty : proc_env_lexical_env_rel (Proc.Empty) (Lexical.Empty)
  | PLExtend :
      forall ctx saved_env (saved_env' : Lexical.environment ctx) val val' x,
        proc_env_lexical_env_rel saved_env saved_env' ->
        proc_val_lexical_val_rel val val' ->
        proc_env_lexical_env_rel (Proc.Extend x val saved_env) (Lexical.Extend val' saved_env')

  with

  proc_val_lexical_val_rel : Proc.expval -> Lexical.expval -> Prop :=
  | PLNum :
      forall num,
        proc_val_lexical_val_rel (Proc.Num num) (Lexical.Num num)
  | PLBool :
      forall bool,
        proc_val_lexical_val_rel (Proc.Bool bool) (Lexical.Bool bool)
  | PLClo :
      forall ctx saved_env (saved_env' : Lexical.environment ctx) senv body body' x,
        proc_env_static_env_rel saved_env senv ->
        translation_of body (Extend x senv) = Some body' ->
        proc_env_lexical_env_rel saved_env saved_env' ->
        proc_val_lexical_val_rel (Proc.Clo x body saved_env) (Lexical.Clo body' saved_env').

  Hint Constructors proc_env_static_env_rel proc_env_lexical_env_rel proc_val_lexical_val_rel.
  Hint Constructors Proc.expression Proc.expval Proc.environment Proc.value_of_rel.
  Hint Constructors Lexical.expression Lexical.expval Lexical.environment Lexical.value_of_rel.
  Hint Constructors static_environment.

  Lemma nth_some :
    forall ctx var (senv : static_environment ctx) n pf env env' (pf' : n < ctx) val,
      find_index var senv = Some (exist _ n pf) ->
      proc_env_static_env_rel env senv ->
      proc_env_lexical_env_rel env env' ->
      Proc.assoc_error var env = Some val ->
      exists val', Lexical.nth env' pf' = val' /\ proc_val_lexical_val_rel val val'.
  Proof.
    intros.
    generalize dependent ctx.
    generalize dependent n.
    generalize dependent var.
    generalize dependent val.
    induction env; intros.
    simpl in H2.
    inversion H2.

    inversion H0.
    subst.
    apply inj_pair2_eq_dec in H9; auto.
    subst.
    simpl in H2.
    simpl in H.
    destruct (string_dec var s).
    inversion H.
    subst.
    inversion H2.
    subst.
    dependent destruction env'.
    simpl.
    exists e.
    inversion H1.
    subst.
    auto.

    destruct (find_index var saved_senv) eqn:?; try congruence.
    destruct s0.
    inversion H.
    subst.
    dependent destruction env'.
    inversion H1.
    subst.
    apply inj_pair2_eq_dec in H11; auto.
    subst.
    specialize (IHenv val).
    specialize (IHenv var).
    apply IHenv with (senv := saved_senv) (env' := env') (pf := l) (pf' := lt_S_n _ _ pf') in H2; auto.
  Qed.

  Lemma assoc_some :
    forall ctx var (senv : static_environment ctx) n pf env env' (pf' : n < ctx) val',
      find_index var senv = Some (exist _ n pf) ->
      proc_env_static_env_rel env senv ->
      proc_env_lexical_env_rel env env' ->
      Lexical.nth env' pf' = val' ->
      exists val, Proc.assoc_error var env = Some val /\ proc_val_lexical_val_rel val val'.
  Proof.
    intros.
    generalize dependent n.
    generalize dependent env.
    generalize dependent var.
    generalize dependent val'.
    dependent induction senv; intros.
    inversion pf.
    destruct n.
    simpl in H.
    destruct (string_dec var s).
    inversion H0.
    apply inj_pair2_eq_dec in H7; auto.
    subst.
    simpl.
    destruct (string_dec s s); try congruence.
    exists val.
    split; auto.
    inversion H1.
    apply inj_pair2_eq_dec in H8; auto.
    subst.
    auto.
    destruct (find_index var senv); try congruence.
    destruct s0.
    inversion H.
    dependent destruction env'.
    inversion H0.
    apply inj_pair2_eq_dec in H7; auto.
    subst.
    inversion H1.
    apply inj_pair2_eq_dec in H9; auto.
    subst.
    simpl in H.
    destruct (string_dec var s).
    inversion H.
    destruct (find_index var senv) eqn:?; try congruence.
    destruct s0.
    inversion H.
    subst.
    specialize (IHsenv env').
    specialize (IHsenv (Lexical.nth (Lexical.Extend e env') pf')).
    specialize (IHsenv var).
    specialize (IHsenv saved_env).
    apply IHsenv with (n0 := n) (pf := l) (pf'0 := lt_S_n _ _ pf') in H6; auto.
    destruct H6.
    destruct H2.
    simpl.
    destruct (string_dec var s); try congruence.
    eauto.
  Qed.

  Lemma translation_of_soundness_generalized :
    forall ctx exp (senv : static_environment ctx) exp' env' val' env,
      translation_of exp senv = Some exp' ->
      Lexical.value_of_rel exp' env' val' ->
      proc_env_static_env_rel env senv ->
      proc_env_lexical_env_rel env env' ->
      exists val,
        proc_val_lexical_val_rel val val' /\
        Proc.value_of_rel exp env val.
  Proof.
    intros.
    generalize dependent exp.
    generalize dependent senv.
    generalize dependent env.
    dependent induction H0; intros.
    apply translation_of_const_inversion in H.
    subst.
    eauto.

    apply translation_of_diff_inversion in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    subst.
    assert (Q1 := H2).
    apply IHvalue_of_rel1 with (senv := senv) (exp := x) in Q1; auto.
    destruct Q1.
    destruct H.
    assert (Q2 := H2).
    apply IHvalue_of_rel2 with (senv := senv) (exp := x0) in Q2; auto.
    destruct Q2.
    destruct H5.
    inversion H.
    inversion H5.
    subst.
    eauto.

    apply translation_of_is_zero_inversion in H.
    destruct H.
    destruct H.
    subst.
    assert (Q1 := H2).
    apply IHvalue_of_rel with (senv := senv) (exp := x) in Q1; auto.
    destruct Q1.
    destruct H.
    inversion H.
    subst.
    eauto.

    apply translation_of_if_inversion in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    destruct H3.
    subst.
    assert (Q1 := H2).
    apply IHvalue_of_rel1 with (senv := senv) (exp := x) in Q1; auto.
    destruct Q1.
    destruct H.
    assert (Q2 := H2).
    apply IHvalue_of_rel2 with (senv := senv) (exp := x0) in Q2; auto.
    destruct Q2.
    destruct H6.
    inversion H.
    subst.
    eauto.

    apply translation_of_if_inversion in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    destruct H3.
    subst.
    assert (Q1 := H2).
    apply IHvalue_of_rel1 with (senv := senv) (exp := x) in Q1; auto.
    destruct Q1.
    destruct H.
    assert (Q2 := H2).
    apply IHvalue_of_rel2 with (senv := senv) (exp := x1) in Q2; auto.
    destruct Q2.
    destruct H6.
    inversion H.
    subst.
    eauto.

    apply translation_of_var_inversion in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    subst.
    assert (T := assoc_some).
    specialize (T ctx).
    specialize (T x).
    specialize (T senv).
    specialize (T n).
    specialize (T x0).
    specialize (T env0).
    specialize (T env).
    specialize (T pf).
    specialize (T (Lexical.nth env pf)).
    apply T in H3; auto.
    destruct H3.
    destruct H.
    eauto.

    apply translation_of_let_inversion in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    subst.
    assert (Q1 := H2).
    apply IHvalue_of_rel1 with (senv := senv) (exp := x0) in Q1; auto.
    destruct Q1.
    destruct H.
    assert (proc_env_lexical_env_rel (Proc.Extend x x2 env0) (Lexical.Extend val1 env)).
    auto.
    apply IHvalue_of_rel2 with (senv := Extend x senv) (exp := x1) in H5; auto.
    destruct H5.
    destruct H5.
    eauto.

    apply translation_of_proc_inversion in H.
    destruct H.
    destruct H.
    destruct H.
    subst.
    eauto.

    apply translation_of_call_inversion in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    subst.
    assert (Q1 := H2).
    apply IHvalue_of_rel1 with (senv := senv) (exp := x) in Q1; auto.
    destruct Q1.
    destruct H.
    assert (Q2 := H2).
    apply IHvalue_of_rel2 with (senv := senv) (exp := x0) in Q2; auto.
    destruct Q2.
    destruct H5.
    inversion H.
    apply inj_pair2_eq_dec in H8; auto.
    apply inj_pair2_eq_dec in H9; auto.
    subst.
    assert (proc_env_lexical_env_rel (Proc.Extend x3 x2 saved_env0) (Lexical.Extend rand_val saved_env)).
    auto.
    apply IHvalue_of_rel3 with (senv := Extend x3 senv0) (exp := body0) in H7; auto.
    destruct H7.
    destruct H7.
    eauto.
  Qed.

  Theorem translation_of_soundness :
    forall exp exp' val',
      translation_of exp Empty = Some exp' ->
      Lexical.value_of_rel exp' Lexical.Empty val' ->
      exists val, proc_val_lexical_val_rel val val' /\ Proc.value_of_rel exp Proc.Empty val.
    intros; eapply translation_of_soundness_generalized; eauto.
  Qed.

  Lemma translation_of_completeness_generalized :
    forall ctx exp (senv : static_environment ctx) exp' env val env',
      translation_of exp senv = Some exp' ->
      Proc.value_of_rel exp env val ->
      proc_env_static_env_rel env senv ->
      proc_env_lexical_env_rel env env' ->
      exists val', proc_val_lexical_val_rel val val' /\ Lexical.value_of_rel exp' env' val'.
  Proof.
    intros.
    generalize dependent ctx.
    induction H0; intros.
    rewrite translation_of_equation in H.
    inversion H.
    subst.
    eauto.

    rewrite translation_of_equation in H.
    destruct (translation_of exp1 senv) eqn:?; try discriminate.
    destruct (translation_of exp2 senv) eqn:?; try discriminate.
    inversion H.
    subst.
    assert (Q1 := H2).
    apply (IHvalue_of_rel1) with (senv := senv) (exp' := e) in Q1; auto.
    destruct Q1.
    destruct H0.
    assert (Q2 := H2).
    apply (IHvalue_of_rel2) with (senv := senv) (exp' := e0) in Q2; auto.
    destruct Q2.
    destruct H4.
    inversion H0.
    subst.
    inversion H4.
    subst.
    eauto.

    rewrite translation_of_equation in H.
    destruct (translation_of exp1 senv) eqn:?; try discriminate.
    inversion H.
    subst.
    assert (Q1 := H2).
    apply (IHvalue_of_rel) with (senv := senv) (exp' := e) in Q1; auto.
    destruct Q1.
    destruct H3.
    inversion H3.
    subst.
    eauto.

    rewrite translation_of_equation in H.
    destruct (translation_of exp1 senv) eqn:?; try discriminate.
    destruct (translation_of exp2 senv) eqn:?; try discriminate.
    destruct (translation_of exp3 senv) eqn:?; try discriminate.
    inversion H.
    subst.
    assert (Q1 := H2).
    apply (IHvalue_of_rel1) with (senv := senv) (exp' := e) in Q1; auto.
    destruct Q1.
    destruct H0.
    assert (Q2 := H2).
    apply (IHvalue_of_rel2) with (senv := senv) (exp' := e0) in Q2; auto.
    destruct Q2.
    destruct H4.
    inversion H0.
    subst.
    eauto.

    rewrite translation_of_equation in H.
    destruct (translation_of exp1 senv) eqn:?; try discriminate.
    destruct (translation_of exp2 senv) eqn:?; try discriminate.
    destruct (translation_of exp3 senv) eqn:?; try discriminate.
    inversion H.
    subst.
    assert (Q1 := H2).
    apply (IHvalue_of_rel1) with (senv := senv) (exp' := e) in Q1; auto.
    destruct Q1.
    destruct H0.
    assert (Q2 := H2).
    apply (IHvalue_of_rel2) with (senv := senv) (exp' := e1) in Q2; auto.
    destruct Q2.
    destruct H4.
    inversion H0.
    subst.
    eauto.

    rewrite translation_of_equation in H0.
    destruct (find_index var senv) eqn:?; try discriminate.
    destruct s.
    inversion H0.
    subst.
    clear H0.
    assert (T := nth_some).
    specialize (T ctx).
    specialize (T var).
    specialize (T senv).
    specialize (T x).
    specialize (T l).
    specialize (T env).
    specialize (T env').
    specialize (T l).
    specialize (T val).
    apply T in Heqo; auto.
    destruct Heqo.
    destruct H0.
    eauto.

    rewrite translation_of_equation in H.
    destruct (translation_of exp1 senv) eqn:?; try discriminate.
    destruct (translation_of body (Extend var senv)) eqn:?; try discriminate.
    inversion H.
    subst.
    assert (Q1 := H2).
    apply IHvalue_of_rel1 with (senv := senv) (exp' := e) in Q1; auto.
    destruct Q1.
    destruct H0.
    assert (proc_env_lexical_env_rel (Proc.Extend var val1 env) (Lexical.Extend x env')).
    auto.
    apply IHvalue_of_rel2 with (senv := Extend var senv) (exp' := e0) in H4; auto.
    destruct H4.
    destruct H4.
    eauto.

    rewrite translation_of_equation in H.
    destruct (translation_of body (Extend var senv)) eqn:?; try discriminate.
    inversion H.
    subst.
    eauto.

    rewrite translation_of_equation in H.
    destruct (translation_of rator senv) eqn:?; try discriminate.
    destruct (translation_of rand senv) eqn:?; try discriminate.
    inversion H.
    subst.
    assert (Q1 := H2).
    apply IHvalue_of_rel1 with (senv := senv) (exp' := e) in Q1; auto.
    destruct Q1.
    destruct H0.
    assert (Q2 := H2).
    apply IHvalue_of_rel2 with (senv := senv) (exp' := e0) in Q2; auto.
    destruct Q2.
    destruct H4.
    inversion H0.
    subst.
    assert (proc_env_lexical_env_rel (Proc.Extend var rand_val saved_env) (Lexical.Extend x0 saved_env')).
    auto.
    apply IHvalue_of_rel3 with (env' := Lexical.Extend x0 saved_env') in H11; auto.
    destruct H11.
    destruct H7.
    eauto.
  Qed.

  Theorem translation_of_completeness :
    forall exp exp' val,
      translation_of exp Empty = Some exp' ->
      Proc.value_of_rel exp Proc.Empty val ->
      exists val', proc_val_lexical_val_rel val val' /\ Lexical.value_of_rel exp' Lexical.Empty val'.
    intros; eapply translation_of_completeness_generalized; eauto.
  Qed.

  Theorem translation_of_correctness :
    forall exp exp',
      translation_of exp Empty = Some exp' ->
      (forall val', Lexical.value_of_rel exp' Lexical.Empty val' ->
               exists val, proc_val_lexical_val_rel val val' /\ Proc.value_of_rel exp Proc.Empty val) /\
      (forall val, Proc.value_of_rel exp Proc.Empty val ->
              exists val', proc_val_lexical_val_rel val val' /\ Lexical.value_of_rel exp' Lexical.Empty val').
  Proof.
    Hint Resolve translation_of_soundness translation_of_completeness.
    intros; eauto.
  Qed.
End Translation.
