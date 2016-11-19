Require Import Bool ZArith Arith List.
Require Import String.
Set Implicit Arguments.

Definition var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.
Infix "==v" := var_eq (no associativity, at level 50).

Module LetSpec.
  Inductive expression : Set :=
  | ExpConst : nat -> expression
  | ExpDiff : expression -> expression -> expression
  | ExpIsZero : expression -> expression
  | ExpIf : expression -> expression -> expression -> expression
  | ExpVar : var -> expression
  | ExpLet : var -> expression -> expression -> expression.

  Implicit Type exp : expression.

  Inductive expval : Set :=
  | ValNum : Z -> expval
  | ValBool : bool -> expval.

  Inductive environment : Set :=
  | EnvEmpty : environment
  | EnvExtend : var -> expval -> environment -> environment.

  Inductive behavior : Set :=
  | BehVal : expval -> behavior
  | BehErr : behavior.

  Coercion BehVal : expval >-> behavior.

  Definition empty_env := EnvEmpty.
  Definition extend_env (env : environment) (x : var) (v : expval) := EnvExtend x v env.
  Fixpoint apply_env (env : environment) (x : var) : behavior :=
    match env with
    | EnvEmpty => BehErr
    | EnvExtend x' v env' => if x' ==v x then v else apply_env env' x
    end.

  Inductive term : Set :=
  | TmExp : expression -> term
  | TmDiff1 : behavior -> expression -> term
  | TmDiff2 : expval -> behavior -> term
  | TmIsZero1 : behavior -> term
  | TmIf1 : behavior -> expression -> expression -> term
  | TmLet1 : var -> behavior -> expression -> term.

  Coercion TmExp : expression >-> term.

  Inductive abort : behavior -> Prop :=
  | AbrErr : abort BehErr.

  Inductive is_num : expval -> Prop :=
  | IsNum : forall n, is_num (ValNum n).

  Inductive is_bool : expval -> Prop :=
  | IsBool : forall b, is_bool (ValBool b).

  Inductive value_of_rel : environment -> term -> behavior -> Prop :=
  | VrelConst :
      forall env n,
        value_of_rel env (ExpConst n) (BehVal (ValNum (Z.of_nat n)))
  | VrelDiff :
      forall env exp1 beh1 exp2 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmDiff1 beh1 exp2) beh ->
        value_of_rel env (ExpDiff exp1 exp2) beh
  | VrefDiff1_abort :
      forall beh1 env exp2,
        abort beh1 ->
        value_of_rel env (TmDiff1 beh1 exp2) beh1
  | VrelDiff1 :
      forall env exp2 beh2 val1 beh,
        value_of_rel env exp2 beh2 ->
        value_of_rel env (TmDiff2 val1 beh2) beh ->
        value_of_rel env (TmDiff1 val1 exp2) beh
  | VrelDiff2_abort :
      forall beh2 env val1,
        abort beh2 ->
        value_of_rel env (TmDiff2 val1 beh2) beh2
  | VrelDiff2 :
      forall env n1 n2,
        value_of_rel env (TmDiff2 (ValNum n1) (ValNum n2)) (ValNum (n1 - n2))
  | VrelDiff2_err :
      forall val1 val2 env,
        ~(is_num val1 /\ is_num val2) ->
        value_of_rel env (TmDiff2 val1 val2) BehErr
  | VrelIsZero :
      forall env exp1 beh1 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmIsZero1 beh1) beh ->
        value_of_rel env (ExpIsZero exp1) beh
  | VrelIsZero1_abort :
      forall beh1 env,
        abort beh1 ->
        value_of_rel env (TmIsZero1 beh1) beh1
  | VrelIsZero1 :
      forall env n1,
        value_of_rel env (TmIsZero1 (ValNum n1)) (ValBool (Z.eqb n1 0))
  | VrelIsZero1_err :
      forall val1 env,
        ~is_num val1 ->
        value_of_rel env (TmIsZero1 val1) BehErr
  | VrelIf :
      forall env exp1 beh1 exp2 exp3 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmIf1 beh1 exp2 exp3) beh ->
        value_of_rel env (ExpIf exp1 exp2 exp3) beh
  | VrelIf1_abort :
      forall beh1 env exp2 exp3,
        abort beh1 ->
        value_of_rel env (TmIf1 beh1 exp2 exp3) beh1
  | VrelIf1_true :
      forall env exp2 beh2 exp3,
        value_of_rel env exp2 beh2 ->
        value_of_rel env (TmIf1 (ValBool true) exp2 exp3) beh2
  | VrelIf1_false :
      forall env exp3 beh3 exp2,
        value_of_rel env exp3 beh3 ->
        value_of_rel env (TmIf1 (ValBool false) exp2 exp3) beh3
  | VrelIf1_err :
      forall val1 env exp2 exp3,
        ~is_bool val1 ->
        value_of_rel env (TmIf1 val1 exp2 exp3) BehErr
  | VrelVar :
      forall env x,
        value_of_rel env (ExpVar x) (apply_env env x)
  | VrelLet :
      forall env exp1 beh1 x exp2 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmLet1 x beh1 exp2) beh ->
        value_of_rel env (ExpLet x exp1 exp2) beh
  | VrelLet1_abort :
      forall beh1 env x exp2,
        abort beh1 ->
        value_of_rel env (TmLet1 x beh1 exp2) beh1
  | VrelLet1 :
      forall env x val1 exp2 beh2,
        value_of_rel (extend_env env x val1) exp2 beh2 ->
        value_of_rel env (TmLet1 x val1 exp2) beh2.

  Hint Constructors expression expval environment behavior term abort is_num is_bool value_of_rel.
End LetSpec.

Module LetImpl.
  Export LetSpec.

  Implicit Type exp : expression.

  Notation "x <- e1 ; e2" :=
    (match e1 with
     | BehVal x => e2
     | BehErr => BehErr
     end)
      (right associativity, at level 60).

  Function value_of (env : environment) (exp : expression) : behavior :=
    match exp with
    | ExpConst n => ValNum (Z.of_nat n)
    | ExpDiff exp1 exp2 =>
      val1 <- value_of env exp1;
        val2 <- value_of env exp2;
        match (val1, val2) with
        | (ValNum n1, ValNum n2) => ValNum (n1 - n2)
        | _ => BehErr
        end
    | ExpIsZero exp1 =>
      val1 <- value_of env exp1;
        match val1 with
        | ValNum n1 => ValBool (Z.eqb n1 0)
        | _ => BehErr
        end
    | ExpIf exp1 exp2 exp3 =>
      val1 <- value_of env exp1;
        match val1 with
        | ValBool true => value_of env exp2
        | ValBool false => value_of env exp3
        | _ => BehErr
        end
    | ExpVar var => apply_env env var
    | ExpLet var exp1 body =>
      val1 <- value_of env exp1;
        value_of (extend_env env var val1) body
    end.

  Hint Extern 3 => match goal with
                  | [ H : is_num (ValBool _) |- _ ] => inversion H
                  | [ H : is_bool (ValNum _) |- _ ] => inversion H
                  | [ |- context[is_num (ValBool _)] ] => intuition
                  | [ |- context[is_bool (ValNum _)] ] => intuition
                  | [ H : ~ _ |- _ ] => contradict H
                  end.

  Theorem value_of_soundness :
    forall env exp beh,
      value_of env exp = beh ->
      value_of_rel env exp beh.
  Proof.
    intros env exp.
    generalize dependent env.
    induction exp; intros; rewrite value_of_equation in *; subst;
      repeat
        (try match goal with
             | [ |- context[match value_of ?ENV ?EXP with BehVal _ => _ | BehErr => _ end] ] =>
               destruct (value_of ENV EXP) eqn:?; try congruence
             | [ |- context[match ?VAL with ValNum _ => _ | ValBool _ => _ end] ] =>
               destruct VAL; try congruence
             | [ |- context[if ?B then _ else _] ] =>
               destruct B
             end;
         eauto 10).
  Qed.

  Ltac invert' H := inversion H; clear H; subst.

  Theorem value_of_completeness :
    forall env exp beh,
      value_of_rel env exp beh ->
      value_of env exp = beh.
  Proof.
    intros env exp.
    generalize dependent env.
    induction exp; intros; rewrite value_of_equation; inversion H; clear H; subst; eauto;
    repeat
      (try match goal with
           | [ H : value_of_rel _ (TmDiff1 _ _) _ |- _ ] =>
             invert' H
           | [ H : value_of_rel _ (TmDiff2 _ _) _ |- _ ] =>
             invert' H
           | [ H : value_of_rel _ (TmIsZero1 _) _ |- _ ] =>
             invert' H
           | [ H : value_of_rel _ (TmIf1 _ _ _) _ |- _ ] =>
             invert' H
           | [ H : value_of_rel _ (TmLet1 _ _ _) _ |- _ ] =>
             invert' H
           | [ IH : forall _ _, value_of_rel _ ?EXP _ -> _, H : value_of_rel _ ?EXP _ |- _ ] =>
             apply IH in H; rewrite H
           | [ H : abort _ |- _ ] =>
             invert' H
           | [ |- context[match ?VAL with ValNum _ => _ | ValBool _ => _ end] ] =>
             destruct VAL; try congruence
           end;
       eauto 10).
  Qed.

  Hint Resolve value_of_soundness value_of_completeness.
  
  Theorem value_of_correctness :
    forall exp beh,
      value_of empty_env exp = beh <->
      value_of_rel empty_env exp beh.
  Proof.
    intuition.
  Qed.
End LetImpl.

Export LetImpl.