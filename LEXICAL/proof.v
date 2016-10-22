Require Import Bool ZArith Arith String List Max.
Set Implicit Arguments.

Notation "x <- e1 ; e2" :=
    (match e1 with
    | None => None
    | Some x => e2
    end)
(right associativity, at level 60).

Lemma option_eq {T : Type} (p q : T) : Some p = Some q -> p = q.
    congruence.
Qed.

Module Proc.
  Inductive expression : Set :=
  | Const : nat -> expression
  | Diff : expression -> expression -> expression
  | IsZero : expression -> expression
  | If : expression -> expression -> expression -> expression
  | Var : string -> expression
  | Let : string -> expression -> expression -> expression
  | Proc : string -> expression -> expression
  | Call : expression -> expression -> expression
  .

  Inductive expval : Set :=
  | Num : Z -> expval
  | Bool : bool -> expval
  | Clo : string -> expression -> list (string * expval) -> expval
  .

  Definition environment := list (string * expval).
  Definition empty_env : environment := nil.
  Definition extend_env (x : string) (v : expval) (env : environment) := (x, v) :: env.

  Fixpoint assoc (x : string) (env : environment) : option expval :=
      match env with
      | nil => None
      | (y, v) :: saved_env => if string_dec x y then Some v else assoc x saved_env
      end.

  Inductive value_of_rel : expression -> environment -> expval -> Prop :=
  | VConst : forall num env, value_of_rel (Const num) env (Num (Z.of_nat num))
  | VDiff : forall exp1 exp2 num1 num2 env, value_of_rel exp1 env (Num num1) -> value_of_rel exp2 env (Num num2) -> value_of_rel (Diff exp1 exp2) env (Num (num1 - num2))
  | VIsZero : forall exp1 num1 env, value_of_rel exp1 env (Num num1) -> value_of_rel (IsZero exp1) env (Bool (Z.eqb num1 0))
  | VIfTrue : forall exp1 exp2 exp3 val2 env, value_of_rel exp1 env (Bool true) -> value_of_rel exp2 env val2 -> value_of_rel (If exp1 exp2 exp3) env val2
  | VIfFalse : forall exp1 exp2 exp3 val3 env, value_of_rel exp1 env (Bool false) -> value_of_rel exp3 env val3 -> value_of_rel (If exp1 exp2 exp3) env val3
  | VVar : forall var env val, assoc var env = Some val -> value_of_rel (Var var) env val
  | VLet : forall var exp1 body env val1 valb, value_of_rel exp1 env val1 -> value_of_rel body (extend_env var val1 env) valb -> value_of_rel (Let var exp1 body) env valb
  | VProc : forall var body env, value_of_rel (Proc var body) env (Clo var body env)
  | VCall : forall rator rand env var body saved_env rand_val valb, value_of_rel rator env (Clo var body saved_env) -> value_of_rel rand env rand_val -> value_of_rel body (extend_env var rand_val saved_env) valb -> value_of_rel (Call rator rand) env valb
  .
End Proc.

Module Lexical.
  Inductive expression : Set :=
  | Const : nat -> expression
  | Diff : expression -> expression -> expression
  | IsZero : expression -> expression
  | If : expression -> expression -> expression -> expression
  | Var : nat -> expression
  | Let : expression -> expression -> expression
  | Proc : expression -> expression
  | Call : expression -> expression -> expression
  .

  Inductive expval : Set :=
  | Num : Z -> expval
  | Bool : bool -> expval
  | Clo : expression -> list expval -> expval
  .

  Definition environment := list expval.
  Definition empty_env : environment := nil.
  Definition extend_env (v : expval) (env : environment) := v :: env.

  Inductive value_of_rel : expression -> environment -> expval -> Prop :=
  | VConst : forall num env, value_of_rel (Const num) env (Num (Z.of_nat num))
  | VDiff : forall exp1 exp2 num1 num2 env, value_of_rel exp1 env (Num num1) -> value_of_rel exp2 env (Num num2) -> value_of_rel (Diff exp1 exp2) env (Num (num1 - num2))
  | VIsZero : forall exp1 num1 env, value_of_rel exp1 env (Num num1) -> value_of_rel (IsZero exp1) env (Bool (Z.eqb num1 0))
  | VIfTrue : forall exp1 exp2 exp3 val2 env, value_of_rel exp1 env (Bool true) -> value_of_rel exp2 env val2 -> value_of_rel (If exp1 exp2 exp3) env val2
  | VIfFalse : forall exp1 exp2 exp3 val3 env, value_of_rel exp1 env (Bool false) -> value_of_rel exp3 env val3 -> value_of_rel (If exp1 exp2 exp3) env val3
  | VVar : forall n env val, nth_error env n = value val -> value_of_rel (Var n) env val
  | VLet : forall exp1 body env val1 valb, value_of_rel exp1 env val1 -> value_of_rel body (extend_env val1 env) valb -> value_of_rel (Let exp1 body) env valb
  | VProc : forall body env, value_of_rel (Proc body) env (Clo body env)
  | VCall : forall rator rand env body saved_env rand_val valb, value_of_rel rator env (Clo body saved_env) -> value_of_rel rand env rand_val -> value_of_rel body (extend_env rand_val saved_env) valb -> value_of_rel (Call rator rand) env valb
  .

  Function value_of (exp : expression) (env : environment) (fuel : nat) : option expval :=
      match fuel with
      | O => None
      | S fuel' =>
              match exp with
              | Const num => Some (Num (Z.of_nat num))
              | Diff exp1 exp2 =>
                      val1 <- value_of exp1 env fuel';
                      val2 <- value_of exp2 env fuel';
                      match (val1, val2) with
                      | (Num num1, Num num2) => Some (Num (num1 - num2))
                      | _ => None
                      end
              | IsZero exp1 =>
                      val1 <- value_of exp1 env fuel';
                      match val1 with
                      | Num num1 => Some (Bool (Z.eqb num1 0))
                      | _ => None
                      end
              | If exp1 exp2 exp3 =>
                      val1 <- value_of exp1 env fuel';
                      match val1 with
                      | Bool true => value_of exp2 env fuel'
                      | Bool false => value_of exp3 env fuel'
                      | _ => None
                      end
              | Var n =>
                      match nth_error env n with
                      | value val => Some val
                      | error => None
                      end
              | Let exp1 body =>
                      val1 <- value_of exp1 env fuel';
                      value_of body (extend_env val1 env) fuel'
              | Proc body => Some (Clo body env)
              | Call rator rand =>
                      rator_val <- value_of rator env fuel';
                      match rator_val with
                      | Clo body saved_env =>
                              rand_val <- value_of rand env fuel';
                              value_of body (extend_env rand_val saved_env) fuel'
                      | _ => None
                      end
              end
      end.

  Hint Constructors value_of_rel.

  Theorem value_of_soundness : forall exp env val, (exists fuel, value_of exp env fuel = Some val) -> value_of_rel exp env val.
      intros.
      destruct 0 as [ fuel ? ].
      generalize dependent val.
      generalize dependent env.
      generalize dependent exp.
      induction fuel; intros; try discriminate; destruct exp;
      match goal with
      | [ H : value_of _ _ _ = _ |- _ ] => simpl in H
      end;
      repeat (try match goal with
                  | [ _ : context[match value_of ?EXP ?ENV ?FUEL with Some _ => _ | None => _ end] |- _ ] => destruct (value_of EXP ENV FUEL) eqn:?; try discriminate
                  | [ _ : context[match ?VAL with Num _ => _ | Bool _ => _ | Clo _ _ => _ end] |- _ ] => destruct VAL; try discriminate
                  | [ _ : context[if ?B then _ else _] |- _ ] => destruct B
                  | [ _ : context[match nth_error ?ENV ?N with value _ => _ | error => _ end] |- _ ] => destruct (nth_error ENV N) eqn:?; try discriminate
                  | [ H : Some _ = Some _ |- _ ] => apply option_eq in H; try (rewrite <- H)
                  end;
              eauto).
  Qed.

  Lemma fuel_incr : forall fuel exp env val, value_of exp env fuel = Some val -> value_of exp env (S fuel) = Some val.
      induction fuel; intros; try discriminate; destruct exp;
      match goal with
      | [ H : value_of _ _ _ = _ |- _ ] => simpl in H
      end;
      rewrite value_of_equation;
      repeat (try match goal with
                  | [ _ : context[match value_of ?EXP ?ENV ?FUEL with Some _ => _ | None => _ end] |- _ ] => destruct (value_of EXP ENV FUEL) eqn:?; try discriminate
                  | [ _ : context[match ?VAL with Num _ => _ | Bool _ => _ | Clo _ _ => _ end] |- _ ] => destruct VAL; try discriminate
                  | [ _ : context[if ?B then _ else _] |- _ ] => destruct B
                  | [ IH : forall _, _, H : value_of ?EXP ?ENV ?FUEL = Some ?VAL |- context[match value_of ?EXP ?ENV (S ?FUEL) with Some _ => _ | None => _ end] ] => assert (T := IH EXP ENV VAL); apply T in H; clear T; try (rewrite -> H; clear H)
                  end;
              eauto).
  Qed.

  Lemma fuel_order : forall exp env val fuel fuel', value_of exp env fuel = Some val -> fuel <= fuel' -> value_of exp env fuel' = Some val.
      Hint Resolve fuel_incr.
      induction 2; auto.
  Qed.

  Lemma le_max_1 : forall a b c, a <= max (max a b) c.
      intros.
      assert (max a (max b c) = max (max a b) c).
      apply max_assoc.
      rewrite <- H.
      apply le_max_l.
  Qed.

  Lemma le_max_2 : forall a b c, b <= max (max a b) c.
      intros.
      assert (b <= max a b).
      apply le_max_r.
      assert (max a b <= max (max a b) c).
      apply le_max_l.
      omega.
  Qed.

  Lemma le_max_3 : forall a b c, c <= max (max a b) c.
      intros.
      apply le_max_r.
  Qed.

  Theorem value_of_completeness : forall exp env val, value_of_rel exp env val -> exists fuel, value_of exp env fuel = Some val.
      Hint Resolve le_max_l le_max_r le_max_1 le_max_2 le_max_3.
      induction 1;
      match goal with
      | [ IH1 : exists _, _, IH2 : exists _, _, IH3 : exists _, _ |- _ ] => destruct IH1 as [ fuel1 ? ]; destruct IH2 as [ fuel2 ? ]; destruct IH3 as [ fuel3 ? ]; exists (S (max (max fuel1 fuel2) fuel3))
      | [ IH1 : exists _, _, IH2 : exists _, _ |- _ ] => destruct IH1 as [ fuel1 ? ]; destruct IH2 as [ fuel2 ? ]; exists (S (max fuel1 fuel2))
      | [ IH1 : exists _, _ |- _ ] => destruct IH1 as [ fuel1 ? ]; exists (S fuel1)
      | [ |- _ ] => exists (S O)
      end;
      eauto;
      rewrite value_of_equation;
      repeat (try match goal with
                  | [ H : value_of ?EXP ?ENV ?FUEL1 = _ |- context[value_of ?EXP ?ENV ?FUEL2] ] => apply fuel_order with (fuel' := FUEL2) in H; auto; try (rewrite -> H; clear H)
                  | [ H : nth_error ?ENV ?N = _ |- context[nth_error ?ENV ?N] ] => destruct (nth_error ENV N)
                  end;
              eauto).
  Qed.

  Theorem value_of_correctness : forall exp env val, (exists fuel, value_of exp env fuel = Some val) <-> value_of_rel exp env val.
      Hint Resolve value_of_soundness value_of_completeness.
      intros; split; auto.
  Qed.
End Lexical.

Module Translation.
  Definition static_environment := list string.
  Definition empty_senv : static_environment := nil.
  Definition extend_senv (x : string) (senv : static_environment) : static_environment := x :: senv.

  Fixpoint find_index (x : string) (senv : static_environment) : option nat :=
      match senv with
      | nil => None
      | y :: saved_senv =>
              if string_dec x y then
                  Some O
              else
                  n <- find_index x saved_senv;
                  Some (S n)
      end.

  Fixpoint translation_of (exp : Proc.expression) (senv : static_environment) : option Lexical.expression :=
      match exp with
      | Proc.Const num => Some (Lexical.Const num)
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
              n <- find_index var senv;
              Some (Lexical.Var n)
      | Proc.Let var exp1 body =>
              exp1 <- translation_of exp1 senv;
              body <- translation_of body (extend_senv var senv);
              Some (Lexical.Let exp1 body)
      | Proc.Proc var body =>
              body <- translation_of body (extend_senv var senv);
              Some (Lexical.Proc body)
      | Proc.Call rator rand =>
              rator <- translation_of rator senv;
              rand <- translation_of rand senv;
              Some (Lexical.Call rator rand)
      end.

  Fixpoint proc_environment_to_static_environment (env : Proc.environment) : static_environment :=
      match env with
      | nil => nil
      | (x, _) :: saved_env => x :: proc_environment_to_static_environment saved_env
      end.

  Fixpoint translation_of_expval (val : Proc.expval) : option Lexical.expval :=
      match val with
      | Proc.Num num => Some (Lexical.Num num)
      | Proc.Bool bool => Some (Lexical.Bool bool)
      | Proc.Clo var body saved_env =>
              body <- translation_of body (extend_senv var (proc_environment_to_static_environment saved_env));
              saved_env <- fold_right (fun pair env =>
                                           val <- translation_of_expval (snd pair);
                                           env <- env;
                                           Some (val :: env)) (Some nil) saved_env;
              Some (Lexical.Clo body saved_env)
      end.

  Definition translation_of_environment (env : Proc.environment) : option Lexical.environment := fold_right (fun pair env =>
                                val <- translation_of_expval (snd pair);
                                env <- env;
                                Some (val :: env)) (Some nil) env.

  Hint Constructors Proc.value_of_rel Lexical.value_of_rel.

  Lemma translation_of_soundness_generalized : forall exp exp' env env' val val' senv, translation_of exp senv = Some exp' -> translation_of_environment env = Some env' -> translation_of_expval val = Some val' -> proc_environment_to_static_environment env = senv -> Lexical.value_of_rel exp' env' val' -> Proc.value_of_rel exp env val.
  Admitted.

  Theorem translation_of_soundness : forall exp exp' val val', translation_of exp empty_senv = Some exp' -> translation_of_expval val = Some val' -> Lexical.value_of_rel exp' Lexical.empty_env val' -> Proc.value_of_rel exp Proc.empty_env val.
      intros; eapply translation_of_soundness_generalized; eauto; auto.
  Qed.

  Lemma translation_of_completeness_generalized : forall exp exp' env env' val val' senv, translation_of exp senv = Some exp' -> translation_of_environment env = Some env' -> translation_of_expval val = Some val' -> Proc.value_of_rel exp env val -> Lexical.value_of_rel exp' env' val'.
  Admitted.

  Theorem translation_of_completeness : forall exp exp' val val', translation_of exp empty_senv = Some exp' -> translation_of_expval val = Some val' -> Proc.value_of_rel exp Proc.empty_env val -> Lexical.value_of_rel exp' Lexical.empty_env val'.
      intros; eapply translation_of_completeness_generalized; eauto; auto.
  Qed.
End Translation.
