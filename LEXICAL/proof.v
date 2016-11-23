Require Import String.
Require Import Bool ZArith Arith List Max.
Require Import Logic.Eqdep_dec Program.Equality.
Set Implicit Arguments.

Axiom prop_ext : forall P Q : Prop, (P <-> Q) -> P = Q.

Definition var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.
Infix "==v" := var_eq (no associativity, at level 50).
  
Module ProcSpec.
  Inductive expression : list var -> Set :=
  | ExpConst : forall fv, nat -> expression fv
  | ExpDiff : forall fv, expression fv -> expression fv -> expression fv
  | ExpIsZero : forall fv, expression fv -> expression fv
  | ExpIf : forall fv, expression fv -> expression fv -> expression fv -> expression fv
  | ExpVar : forall x fv, In x fv -> expression fv
  | ExpLet : forall fv x, expression fv -> expression (x :: fv) -> expression fv
  | ExpProc : forall x fv, expression (x :: fv) -> expression fv
  | ExpCall : forall fv, expression fv -> expression fv -> expression fv.

  Inductive expval : Set :=
  | ValNum : Z -> expval
  | ValBool : bool -> expval
  | ValClo : forall x fv, expression (x :: fv) -> environment fv -> expval

  with environment : list var -> Set :=
       | EnvEmpty : environment nil
       | EnvExtend : forall fv x, expval -> environment fv -> environment (x :: fv).

  Inductive behavior : Set :=
  | BehVal : expval -> behavior
  | BehErr : behavior.

  Coercion BehVal : expval >-> behavior.

  Definition empty_env := EnvEmpty.
  Definition extend_env {fv} (env : environment fv) (x : var) (v : expval) := EnvExtend x v env.

  Lemma x_in_empty : forall x : var, In x nil -> False.
    auto.
  Qed.

  Lemma x_in_extend : forall (x' x : var) fv, x' <> x -> In x (x' :: fv) -> In x fv.
    simpl; intuition.
  Qed.
  
  Fixpoint apply_env {fv} (env : environment fv) (x : var) : List.In x fv -> expval :=
    match env in (environment fv) with
    | EnvEmpty => fun pf => match x_in_empty pf with end
    | EnvExtend x' v env' =>
      match x' ==v x with
      | left _ => fun _ => v
      | right ne => fun pf => apply_env env' x (x_in_extend ne pf)
      end
    end.

  Inductive term : list var -> Set :=
  | TmExp : forall fv, expression fv -> term fv
  | TmDiff1 : forall fv, behavior -> expression fv -> term fv
  | TmDiff2 : forall fv, expval -> behavior -> term fv
  | TmIsZero1 : forall fv, behavior -> term fv
  | TmIf1 : forall fv, behavior -> expression fv -> expression fv -> term fv
  | TmLet1 : forall x fv, behavior -> expression (x :: fv) -> term fv
  | TmCall1 : forall fv, behavior -> expression fv -> term fv
  | TmCall2 : forall fv, expval -> behavior -> term fv.

  Coercion TmExp : expression >-> term.

  Inductive abort : behavior -> Prop :=
  | AbrErr : abort BehErr.

  Inductive is_num : expval -> Prop :=
  | IsNum : forall n, is_num (ValNum n).

  Inductive is_bool : expval -> Prop :=
  | IsBool : forall b, is_bool (ValBool b).

  Inductive is_clo : expval -> Prop :=
  | IsClo : forall x fv (exp1 : expression (x :: fv)) (saved_env : environment fv), is_clo (ValClo exp1 saved_env).

  Inductive value_of_rel : forall fv, environment fv -> term fv -> behavior -> Prop :=
  | VrelConst :
      forall fv (env : environment fv) n,
        value_of_rel env (ExpConst fv n) (ValNum (Z.of_nat n))
  | VrelDiff :
      forall fv env (exp1 : expression fv) beh1 exp2 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmDiff1 beh1 exp2) beh ->
        value_of_rel env (ExpDiff exp1 exp2) beh
  | VrefDiff1_abort :
      forall fv beh1 (env : environment fv) exp2,
        abort beh1 ->
        value_of_rel env (TmDiff1 beh1 exp2) beh1
  | VrelDiff1 :
      forall fv env (exp2 : expression fv) beh2 val1 beh,
        value_of_rel env exp2 beh2 ->
        value_of_rel env (TmDiff2 fv val1 beh2) beh ->
        value_of_rel env (TmDiff1 val1 exp2) beh
  | VrelDiff2_abort :
      forall fv beh2 env val1,
        abort beh2 ->
        value_of_rel env (TmDiff2 fv val1 beh2) beh2
  | VrelDiff2 :
      forall fv env n1 n2,
        value_of_rel env (TmDiff2 fv (ValNum n1) (ValNum n2)) (ValNum (n1 - n2))
  | VrelDiff2_err :
      forall fv val1 val2 env,
        ~(is_num val1 /\ is_num val2) ->
        value_of_rel env (TmDiff2 fv val1 val2) BehErr
  | VrelIsZero :
      forall fv env (exp1 : expression fv) beh1 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmIsZero1 fv beh1) beh ->
        value_of_rel env (ExpIsZero exp1) beh
  | VrelIsZero1_abort :
      forall fv beh1 env,
        abort beh1 ->
        value_of_rel env (TmIsZero1 fv beh1) beh1
  | VrelIsZero1 :
      forall fv env n1,
        value_of_rel env (TmIsZero1 fv (ValNum n1)) (ValBool (Z.eqb n1 0))
  | VrelIsZero1_err :
      forall fv val1 env,
        ~is_num val1 ->
        value_of_rel env (TmIsZero1 fv val1) BehErr
  | VrelIf :
      forall fv env (exp1 : expression fv) beh1 exp2 exp3 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmIf1 beh1 exp2 exp3) beh ->
        value_of_rel env (ExpIf exp1 exp2 exp3) beh
  | VrelIf1_abort :
      forall fv beh1 (env : environment fv) exp2 exp3,
        abort beh1 ->
        value_of_rel env (TmIf1 beh1 exp2 exp3) beh1
  | VrelIf1_true :
      forall fv env (exp2 : expression fv) beh2 exp3,
        value_of_rel env exp2 beh2 ->
        value_of_rel env (TmIf1 (ValBool true) exp2 exp3) beh2
  | VrelIf1_false :
      forall fv env (exp3 : expression fv) beh3 exp2,
        value_of_rel env exp3 beh3 ->
        value_of_rel env (TmIf1 (ValBool false) exp2 exp3) beh3
  | VrelIf1_err :
      forall fv val1 (env : environment fv) exp2 exp3,
        ~is_bool val1 ->
        value_of_rel env (TmIf1 val1 exp2 exp3) BehErr
  | VrelVar :
      forall fv env x (pf : In x fv),
        value_of_rel env (ExpVar x fv pf) (apply_env env x pf)
  | VrelLet :
      forall fv env (exp1 : expression fv) beh1 x (exp2 : expression (x :: fv)) beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmLet1 beh1 exp2) beh ->
        value_of_rel env (ExpLet exp1 exp2) beh
  | VrelLet1_abort :
      forall fv beh1 env x (exp2 : expression (x :: fv)),
        abort beh1 ->
        value_of_rel env (TmLet1 beh1 exp2) beh1
  | VrelLet1 :
      forall fv env x val1 (exp2 : expression (x :: fv)) beh2,
        value_of_rel (extend_env env x val1) exp2 beh2 ->
        value_of_rel env (TmLet1 val1 exp2) beh2
  | VrelProc :
      forall fv env x (exp1 : expression (x :: fv)),
        value_of_rel env (ExpProc exp1) (ValClo exp1 env)
  | VrelCall :
      forall fv env (exp1 : expression fv) beh1 exp2 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmCall1 beh1 exp2) beh ->
        value_of_rel env (ExpCall exp1 exp2) beh
  | VrelCall1_abort :
      forall fv beh1 env (exp2 : expression fv),
        abort beh1 ->
        value_of_rel env (TmCall1 beh1 exp2) beh1
  | VrelCall1 :
      forall fv env (exp2 : expression fv) beh2 val1 beh,
        value_of_rel env exp2 beh2 ->
        value_of_rel env (TmCall2 fv val1 beh2) beh ->
        value_of_rel env (TmCall1 val1 exp2) beh
  | VrelCall2_abort :
      forall fv beh2 env val1,
        abort beh2 ->
        value_of_rel env (TmCall2 fv val1 beh2) beh2
  | VrelCall2 :
      forall fv saved_env x val2 (exp1 : expression (x :: fv)) beh env,
        value_of_rel (extend_env saved_env x val2) exp1 beh ->
        value_of_rel env (TmCall2 fv (ValClo exp1 saved_env) val2) beh
  | VrelCall2_err :
      forall fv val1 env val2,
        ~is_clo val1 ->
        value_of_rel env (TmCall2 fv val1 val2) BehErr.

  Hint Constructors expression expval environment behavior term abort is_num is_bool is_clo value_of_rel.
End ProcSpec.

Module LexicalSpec.
  Inductive expression : nat -> Set :=
  | ExpConst : forall ctx, nat -> expression ctx
  | ExpDiff : forall ctx, expression ctx -> expression ctx -> expression ctx
  | ExpIsZero : forall ctx, expression ctx -> expression ctx
  | ExpIf : forall ctx, expression ctx -> expression ctx -> expression ctx -> expression ctx
  | ExpVar : forall n ctx, n < ctx -> expression ctx
  | ExpLet : forall ctx, expression ctx -> expression (S ctx) -> expression ctx
  | ExpProc : forall ctx, expression (S ctx) -> expression ctx
  | ExpCall : forall ctx, expression ctx -> expression ctx -> expression ctx.

  Inductive expval : Set :=
  | ValNum : Z -> expval
  | ValBool : bool -> expval
  | ValClo : forall ctx, expression (S ctx) -> environment ctx -> expval

  with environment : nat -> Set :=
       | EnvEmpty : environment 0
       | EnvExtend : forall ctx, expval -> environment ctx -> environment (S ctx).

  Inductive behavior : Set :=
  | BehVal : expval -> behavior
  | BehErr : behavior.

  Coercion BehVal : expval >-> behavior.

  Definition empty_env := EnvEmpty.
  Definition extend_env {ctx} (env : environment ctx) (v : expval) := EnvExtend v env.

  Lemma n_lt_z : forall n, n < 0 -> False.
    intuition omega.
  Qed.

  Fixpoint apply_env {ctx} (env : environment ctx) (n : nat) : n < ctx -> expval :=
    match env in (environment ctx) with
    | EnvEmpty => fun pf => match n_lt_z pf with end
    | EnvExtend v env' =>
      match n with
      | O => fun _ => v
      | S _ => fun pf => apply_env env' (lt_S_n _ _ pf)
      end
    end.

  Inductive term : nat -> Set :=
  | TmExp : forall ctx, expression ctx -> term ctx
  | TmDiff1 : forall ctx, behavior -> expression ctx -> term ctx
  | TmDiff2 : forall ctx, expval -> behavior -> term ctx
  | TmIsZero1 : forall ctx, behavior -> term ctx
  | TmIf1 : forall ctx, behavior -> expression ctx -> expression ctx -> term ctx
  | TmLet1 : forall ctx, behavior -> expression (S ctx) -> term ctx
  | TmCall1 : forall ctx, behavior -> expression ctx -> term ctx
  | TmCall2 : forall ctx, expval -> behavior -> term ctx.

  Coercion TmExp : expression >-> term.

  Inductive abort : behavior -> Prop :=
  | AbrErr : abort BehErr.

  Inductive is_num : expval -> Prop :=
  | IsNum : forall n, is_num (ValNum n).

  Inductive is_bool : expval -> Prop :=
  | IsBool : forall b, is_bool (ValBool b).

  Inductive is_clo : expval -> Prop :=
  | IsClo : forall ctx (exp1 : expression (S ctx)) (saved_env : environment ctx), is_clo (ValClo exp1 saved_env).

  Inductive value_of_rel : forall ctx, environment ctx -> term ctx -> behavior -> Prop :=
  | VrelConst :
      forall ctx (env : environment ctx) n,
        value_of_rel env (ExpConst ctx n) (ValNum (Z.of_nat n))
  | VrelDiff :
      forall ctx env (exp1 : expression ctx) beh1 exp2 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmDiff1 beh1 exp2) beh ->
        value_of_rel env (ExpDiff exp1 exp2) beh
  | VrefDiff1_abort :
      forall ctx beh1 (env : environment ctx) exp2,
        abort beh1 ->
        value_of_rel env (TmDiff1 beh1 exp2) beh1
  | VrelDiff1 :
      forall ctx env (exp2 : expression ctx) beh2 val1 beh,
        value_of_rel env exp2 beh2 ->
        value_of_rel env (TmDiff2 ctx val1 beh2) beh ->
        value_of_rel env (TmDiff1 val1 exp2) beh
  | VrelDiff2_abort :
      forall ctx beh2 env val1,
        abort beh2 ->
        value_of_rel env (TmDiff2 ctx val1 beh2) beh2
  | VrelDiff2 :
      forall ctx env n1 n2,
        value_of_rel env (TmDiff2 ctx (ValNum n1) (ValNum n2)) (ValNum (n1 - n2))
  | VrelDiff2_err :
      forall ctx val1 val2 env,
        ~(is_num val1 /\ is_num val2) ->
        value_of_rel env (TmDiff2 ctx val1 val2) BehErr
  | VrelIsZero :
      forall ctx env (exp1 : expression ctx) beh1 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmIsZero1 ctx beh1) beh ->
        value_of_rel env (ExpIsZero exp1) beh
  | VrelIsZero1_abort :
      forall ctx beh1 env,
        abort beh1 ->
        value_of_rel env (TmIsZero1 ctx beh1) beh1
  | VrelIsZero1 :
      forall ctx env n1,
        value_of_rel env (TmIsZero1 ctx (ValNum n1)) (ValBool (Z.eqb n1 0))
  | VrelIsZero1_err :
      forall ctx val1 env,
        ~is_num val1 ->
        value_of_rel env (TmIsZero1 ctx val1) BehErr
  | VrelIf :
      forall ctx env (exp1 : expression ctx) beh1 exp2 exp3 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmIf1 beh1 exp2 exp3) beh ->
        value_of_rel env (ExpIf exp1 exp2 exp3) beh
  | VrelIf1_abort :
      forall ctx beh1 (env : environment ctx) exp2 exp3,
        abort beh1 ->
        value_of_rel env (TmIf1 beh1 exp2 exp3) beh1
  | VrelIf1_true :
      forall ctx env (exp2 : expression ctx) beh2 exp3,
        value_of_rel env exp2 beh2 ->
        value_of_rel env (TmIf1 (ValBool true) exp2 exp3) beh2
  | VrelIf1_false :
      forall ctx env (exp3 : expression ctx) beh3 exp2,
        value_of_rel env exp3 beh3 ->
        value_of_rel env (TmIf1 (ValBool false) exp2 exp3) beh3
  | VrelIf1_err :
      forall ctx val1 (env : environment ctx) exp2 exp3,
        ~is_bool val1 ->
        value_of_rel env (TmIf1 val1 exp2 exp3) BehErr
  | VrelVar :
      forall ctx env n (pf : n < ctx),
        value_of_rel env (ExpVar pf) (apply_env env pf)
  | VrelLet :
      forall ctx env (exp1 : expression ctx) beh1 (exp2 : expression (S ctx)) beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmLet1 beh1 exp2) beh ->
        value_of_rel env (ExpLet exp1 exp2) beh
  | VrelLet1_abort :
      forall ctx beh1 env (exp2 : expression (S ctx)),
        abort beh1 ->
        value_of_rel env (TmLet1 beh1 exp2) beh1
  | VrelLet1 :
      forall ctx env val1 (exp2 : expression (S ctx)) beh2,
        value_of_rel (extend_env env val1) exp2 beh2 ->
        value_of_rel env (TmLet1 val1 exp2) beh2
  | VrelProc :
      forall ctx env (exp1 : expression (S ctx)),
        value_of_rel env (ExpProc exp1) (ValClo exp1 env)
  | VrelCall :
      forall ctx env (exp1 : expression ctx) beh1 exp2 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmCall1 beh1 exp2) beh ->
        value_of_rel env (ExpCall exp1 exp2) beh
  | VrelCall1_abort :
      forall ctx beh1 env (exp2 : expression ctx),
        abort beh1 ->
        value_of_rel env (TmCall1 beh1 exp2) beh1
  | VrelCall1 :
      forall ctx env (exp2 : expression ctx) beh2 val1 beh,
        value_of_rel env exp2 beh2 ->
        value_of_rel env (TmCall2 ctx val1 beh2) beh ->
        value_of_rel env (TmCall1 val1 exp2) beh
  | VrelCall2_abort :
      forall ctx beh2 env val1,
        abort beh2 ->
        value_of_rel env (TmCall2 ctx val1 beh2) beh2
  | VrelCall2 :
      forall ctx saved_env val2 (exp1 : expression (S ctx)) beh env,
        value_of_rel (extend_env saved_env val2) exp1 beh ->
        value_of_rel env (TmCall2 ctx (ValClo exp1 saved_env) val2) beh
  | VrelCall2_err :
      forall ctx val1 env val2,
        ~is_clo val1 ->
        value_of_rel env (TmCall2 ctx val1 val2) BehErr.

  Hint Constructors expression expval environment behavior term abort is_num is_bool is_clo value_of_rel.
End LexicalSpec.

Module TranslationImpl.
  Module P := ProcSpec.
  Module L := LexicalSpec.

  Definition index : forall fv (x : var), In x fv -> { n | n < length fv }.
    refine (
        fix F {fv : list var} {x : var} : In x fv -> { n | n < length fv } :=
          match fv with
          | nil => fun pf => match P.x_in_empty pf with end
          | x' :: fv' =>
            match x' ==v x with
            | left _ => fun _ => exist _ 0 _
            | right ne => fun pf =>
                           match F (P.x_in_extend ne pf) with
                           | exist _ n _ => exist _ n _
                           end
            end
          end);
    simpl; omega.
  Defined.

  Function translation_of {fv : list var} (exp : P.expression fv) : L.expression (length fv) :=
    match exp in (P.expression fv) with
    | P.ExpConst _ n => L.ExpConst _ n
    | P.ExpDiff exp1 exp2 =>
      let exp1 := translation_of exp1 in
      let exp2 := translation_of exp2 in
      L.ExpDiff exp1 exp2
    | P.ExpIsZero exp1 =>
      let exp1 := translation_of exp1 in
      L.ExpIsZero exp1
    | P.ExpIf exp1 exp2 exp3 =>
      let exp1 := translation_of exp1 in
      let exp2 := translation_of exp2 in
      let exp3 := translation_of exp3 in
      L.ExpIf exp1 exp2 exp3
    | P.ExpVar x fv pf =>
      match index fv x pf with
      | exist _ _ pflt => L.ExpVar pflt
      end
    | P.ExpLet exp1 exp2 =>
      let exp1 := translation_of exp1 in
      let exp2 := translation_of exp2 in
      L.ExpLet exp1 exp2
    | P.ExpProc exp1 =>
      let exp1 := translation_of exp1 in
      L.ExpProc exp1
    | P.ExpCall exp1 exp2 =>
      let exp1 := translation_of exp1 in
      let exp2 := translation_of exp2 in
      L.ExpCall exp1 exp2
    end.

  Function translation_of_expval (val : P.expval) : L.expval :=
    match val with
    | P.ValNum n => L.ValNum n
    | P.ValBool b => L.ValBool b
    | P.ValClo exp1 saved_env => L.ValClo (translation_of exp1) (translation_of_environment saved_env)
    end

  with translation_of_environment {fv : list var} (env : P.environment fv) : L.environment (length fv) :=
         match env with
         | P.EnvEmpty => L.EnvEmpty
         | P.EnvExtend x val env' => L.EnvExtend (translation_of_expval val) (translation_of_environment env')
         end.

  Definition translation_of_behavior (beh : P.behavior) : L.behavior :=
    match beh with
    | P.BehVal val => L.BehVal (translation_of_expval val)
    | P.BehErr => L.BehErr
    end.

  Definition translation_of_term {fv : list var} (tm : P.term fv) : L.term (length fv) :=
    match tm in (P.term fv) with
    | P.TmExp exp =>
      let exp := translation_of exp in
      L.TmExp exp
    | P.TmDiff1 beh1 exp2 =>
      let beh1 := translation_of_behavior beh1 in
      let exp2 := translation_of exp2 in
      L.TmDiff1 beh1 exp2
    | P.TmDiff2 fv val1 beh2 =>
      let val1 := translation_of_expval val1 in
      let beh2 := translation_of_behavior beh2 in
      L.TmDiff2 (length fv) val1 beh2
    | P.TmIsZero1 fv beh1 =>
      let beh1 := translation_of_behavior beh1 in
      L.TmIsZero1 (length fv) beh1
    | P.TmIf1 beh1 exp2 exp3 =>
      let beh1 := translation_of_behavior beh1 in
      let exp2 := translation_of exp2 in
      let exp3 := translation_of exp3 in
      L.TmIf1 beh1 exp2 exp3
    | P.TmLet1 beh1 exp2 =>
      let beh1 := translation_of_behavior beh1 in
      let exp2 := translation_of exp2 in
      L.TmLet1 beh1 exp2
    | P.TmCall1 beh1 exp2 =>
      let beh1 := translation_of_behavior beh1 in
      let exp2 := translation_of exp2 in
      L.TmCall1 beh1 exp2
    | P.TmCall2 fv val1 beh2 =>
      let val1 := translation_of_expval val1 in
      let beh2 := translation_of_behavior beh2 in
      L.TmCall2 (length fv) val1 beh2
    end.

  Hint Resolve eq_nat_dec.

  Ltac invert' H := inversion H; clear H; subst.
  Ltac existT_invert' H := apply inj_pair2_eq_dec in H; eauto; subst.

  Theorem translation_of_term_soundness :
    forall fv (env : P.environment fv) env' tm tm' beh beh',
      translation_of_environment env = env' ->
      translation_of_term tm = tm' ->
      translation_of_behavior beh = beh' ->
      L.value_of_rel env' tm' beh' ->
      P.value_of_rel env tm beh.
  Proof.
    intros.
    generalize dependent env.
    generalize dependent tm.
    generalize dependent beh.
    dependent induction H2; intros.

    unfold translation_of_behavior in *.
    destruct beh; try congruence.
    unfold translation_of_term in *.
    dependent destruction tm; try discriminate.
    invert' H1.
    invert' H0.
    existT_invert' H1.
    rewrite translation_of_expval_equation in *.
    destruct e; try congruence.
    invert' H3.
    rewrite translation_of_equation in *.
    destruct e0; try discriminate.
    invert' H1.
    eauto.
    destruct (index fv x i); discriminate.
  Admitted.

  Theorem translation_of_soundness :
    forall (exp : P.expression nil) exp' beh beh',
      translation_of exp = exp' ->
      translation_of_behavior beh = beh' ->
      L.value_of_rel L.EnvEmpty (L.TmExp exp') beh' ->
      P.value_of_rel P.EnvEmpty (P.TmExp exp) beh.
  Proof.
    intros; simpl; subst; eapply translation_of_term_soundness; eauto.
  Qed.

  Theorem translation_of_term_completeness :
    forall fv (env : P.environment fv) env' tm tm' beh beh',
      translation_of_environment env = env' ->
      translation_of_term tm = tm' ->
      translation_of_behavior beh = beh' ->
      P.value_of_rel env tm beh ->
      L.value_of_rel env' tm' beh'.
  Proof.
  Admitted.
    
  Theorem translation_of_completeness :
    forall (exp : P.expression nil) exp' beh beh',
      translation_of exp = exp' ->
      translation_of_behavior beh = beh' ->
      P.value_of_rel P.EnvEmpty (P.TmExp exp) beh ->
      L.value_of_rel L.EnvEmpty (L.TmExp exp') beh'.
  Proof.
    intros.
    assert (translation_of_environment P.EnvEmpty = L.EnvEmpty); eauto.
    eapply translation_of_term_completeness in H2; eauto.
    simpl; subst; eauto.
  Qed.

  Hint Resolve translation_of_soundness translation_of_completeness.

  Theorem translation_of_correctness :
    forall (exp : P.expression nil) exp' beh beh',
      translation_of exp = exp' ->
      translation_of_behavior beh = beh' ->
      L.value_of_rel L.EnvEmpty (L.TmExp exp') beh' <->
      P.value_of_rel P.EnvEmpty (P.TmExp exp) beh.
  Proof.
    intuition eauto.
  Qed.
End TranslationImpl.

Export TranslationImpl.