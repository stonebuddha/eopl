Require Import Bool ZArith Arith List.
Require Import Var Map.
Set Implicit Arguments.

Notation "x <- e1 ; e2" :=
  (match e1 with
   | Some x => e2
   | None => None
   end)
    (right associativity, at level 60).

Module LetSpec.
  Inductive expression : Set :=
  | ExpConst : nat -> expression
  | ExpDiff : expression -> expression -> expression
  | ExpIsZero : expression -> expression
  | ExpIf : expression -> expression -> expression -> expression
  | ExpVar : var -> expression
  | ExpLet : var -> expression -> expression -> expression.

  Inductive expval : Set :=
  | ValNum : Z -> expval
  | ValBool : bool -> expval.

  Inductive value_of_rel : expression -> fmap var expval -> expval -> Prop :=
  | VrelConst :
      forall n env,
        value_of_rel (ExpConst n) env (ValNum (Z.of_nat n))
  | VrelDiff :
      forall exp1 exp2 n1 n2 env,
        value_of_rel exp1 env (ValNum n1) ->
        value_of_rel exp2 env (ValNum n2) ->
        value_of_rel (ExpDiff exp1 exp2) env (ValNum (n1 - n2))
  | VrelIsZero :
      forall exp1 n1 env,
        value_of_rel exp1 env (ValNum n1) ->
        value_of_rel (ExpIsZero exp1) env (ValBool (Z.eqb n1 0))
  | VrelIfTrue :
      forall exp1 exp2 exp3 val2 env,
        value_of_rel exp1 env (ValBool true) ->
        value_of_rel exp2 env val2 ->
        value_of_rel (ExpIf exp1 exp2 exp3) env val2
  | VrelIfFalse :
      forall exp1 exp2 exp3 val3 env,
        value_of_rel exp1 env (ValBool false) ->
        value_of_rel exp3 env val3 ->
        value_of_rel (ExpIf exp1 exp2 exp3) env val3
  | VrelVar :
      forall var env val,
        env $? var = Some val -> value_of_rel (ExpVar var) env val
  | VrelLet :
      forall var exp1 body env val1 valb,
        value_of_rel exp1 env val1 ->
        value_of_rel body (env $+ (var, val1)) valb ->
        value_of_rel (ExpLet var exp1 body) env valb.

  Hint Constructors expression expval value_of_rel.
End LetSpec.

Module LetImpl.
  Export LetSpec.

  Inductive environment : Set :=
  | Empty : environment
  | Extend : var -> expval -> environment -> environment.

  Hint Constructors environment.

  Definition empty_env : environment := Empty.

  Fixpoint apply_env (env : environment) x :=
    match env with
    | Empty => None
    | Extend x' v env' => if x ==v x' then Some v else apply_env env' x
    end.

  Definition extend_env (x : var) (v : expval) (env : environment) := Extend x v env.

  Definition implemented env m := forall x, apply_env env x = m $? x.

  Theorem implemented_empty : implemented empty_env $0.
    unfold implemented, empty_env, apply_env.
    intros.
    autorewrite with core.
    auto.
  Qed.

  Hint Resolve implemented_empty.

  Theorem implemented_extend :
    forall env m x v,
      implemented env m ->
      implemented (extend_env x v env) (m $+ (x, v)).
  Proof.
    unfold implemented, extend_env, apply_env.
    intros.
    destruct (x0 ==v x); autorewrite with core; auto.
  Qed.

  Hint Resolve implemented_extend.

  Function value_of (exp : expression) (env : environment) : option expval :=
    match exp with
    | ExpConst n => Some (ValNum (Z.of_nat n))
    | ExpDiff exp1 exp2 =>
      val1 <- value_of exp1 env;
        val2 <- value_of exp2 env;
        match (val1, val2) with
        | (ValNum n1, ValNum n2) => Some (ValNum (n1 - n2))
        | _ => None
        end
    | ExpIsZero exp1 =>
      val1 <- value_of exp1 env;
        match val1 with
        | ValNum n1 => Some (ValBool (Z.eqb n1 0))
        | _ => None
        end
    | ExpIf exp1 exp2 exp3 =>
      val1 <- value_of exp1 env;
        match val1 with
        | ValBool true => value_of exp2 env
        | ValBool false => value_of exp3 env
        | _ => None
        end
    | ExpVar var => apply_env env var
    | ExpLet var exp1 body =>
      val1 <- value_of exp1 env;
        value_of body (extend_env var val1 env)
    end.

  Theorem value_of_soundness :
    forall exp env val,
      value_of exp env = Some val ->
      forall m,
      implemented env m ->
      value_of_rel exp m val.
  Proof.
    induction exp; intros; rewrite value_of_equation in *;
      repeat match goal with
             | [ _ : context[match value_of ?EXP ?ENV with Some _ => _ | None => _ end] |- _ ] =>
               destruct (value_of EXP ENV) eqn:?; try congruence
             | [ _ : context[if ?B then _ else _] |- _ ] =>
               destruct B
             | [ _ : context[match ?VAL with ValNum _ => _ | ValBool _ => _ end] |- _ ] =>
               destruct VAL; try congruence
             | [ H : Some _ = Some _ |- _ ] =>
               inversion H; clear H; subst
             | [ H : implemented _ _ |- _ ] =>
               unfold implemented in H; rewrite H in *
             end;
      eauto.
  Qed.
  
  Theorem value_of_completeness :
    forall exp m val,
      value_of_rel exp m val ->
      forall env,
      implemented env m ->
      value_of exp env = Some val.
  Proof.
    induction 1; intros; rewrite value_of_equation;
      repeat match goal with
             | [ H : forall _, implemented _ _ -> value_of _ _ = _ |- _ ] =>
               rewrite H; clear H; subst; eauto
             | [ H : implemented _ _ |- _ ] =>
               unfold implemented in H; rewrite H in *
             end;
      eauto.
  Qed.

  Hint Resolve value_of_soundness value_of_completeness.
  
  Theorem value_of_correctness :
    forall exp val,
      value_of exp empty_env = Some val <->
      value_of_rel exp $0 val.
  Proof.
    split; eauto.
  Qed.
End LetImpl.

Export LetImpl.