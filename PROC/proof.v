Require Import Bool ZArith Arith List Max.
Require Import String.
Set Implicit Arguments.

Definition var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.
Infix "==v" := var_eq (no associativity, at level 50).

Module ProcSpec.
  Inductive expression : Set :=
  | ExpConst : nat -> expression
  | ExpDiff : expression -> expression -> expression
  | ExpIsZero : expression -> expression
  | ExpIf : expression -> expression -> expression -> expression
  | ExpVar : var -> expression
  | ExpLet : var -> expression -> expression -> expression
  | ExpProc : var -> expression -> expression
  | ExpCall : expression -> expression -> expression.

  Implicit Type exp : expression.

  Inductive expval : Set :=
  | ValNum : Z -> expval
  | ValBool : bool -> expval
  | ValClo : var -> expression -> environment -> expval

  with environment : Set :=
       | EnvEmpty : environment
       | EnvExtend : var -> expval -> environment -> environment. 

  Implicit Type val : expval.
  Implicit Type env : environment.

  Inductive behavior : Set :=
  | BehVal : expval -> behavior
  | BehErr : behavior
  | BehDiv : behavior.

  Implicit Type beh : behavior.

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
  | TmLet1 : var -> behavior -> expression -> term
  | TmCall1 : behavior -> expression -> term
  | TmCall2 : expval -> behavior -> term.

  Coercion TmExp : expression >-> term.

  Inductive abort : behavior -> Prop :=
  | AbrErr : abort BehErr
  | AbrDiv : abort BehDiv.

  Inductive is_num : expval -> Prop :=
  | IsNum : forall n, is_num (ValNum n).

  Inductive is_bool : expval -> Prop :=
  | IsBool : forall b, is_bool (ValBool b).

  Inductive is_clo : expval -> Prop :=
  | IsClo : forall x exp1 saved_env, is_clo (ValClo x exp1 saved_env).

  Inductive value_of_rel : environment -> term -> behavior -> Prop :=
  | VrelConst :
      forall env n,
        value_of_rel env (ExpConst n) (ValNum (Z.of_nat n))
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
        value_of_rel env (TmLet1 x val1 exp2) beh2
  | VrelProc :
      forall env x exp1,
        value_of_rel env (ExpProc x exp1) (ValClo x exp1 env)
  | VrelCall :
      forall env exp1 beh1 exp2 beh,
        value_of_rel env exp1 beh1 ->
        value_of_rel env (TmCall1 beh1 exp2) beh ->
        value_of_rel env (ExpCall exp1 exp2) beh
  | VrelCall1_abort :
      forall beh1 env exp2,
        abort beh1 ->
        value_of_rel env (TmCall1 beh1 exp2) beh1
  | VrelCall1 :
      forall env exp2 beh2 val1 beh,
        value_of_rel env exp2 beh2 ->
        value_of_rel env (TmCall2 val1 beh2) beh ->
        value_of_rel env (TmCall1 val1 exp2) beh
  | VrelCall2_abort :
      forall beh2 env val1,
        abort beh2 ->
        value_of_rel env (TmCall2 val1 beh2) beh2
  | VrelCall2 :
      forall saved_env x val2 exp1 beh env,
        value_of_rel (extend_env saved_env x val2) exp1 beh ->
        value_of_rel env (TmCall2 (ValClo x exp1 saved_env) val2) beh
  | VrelCall2_err :
      forall val1 env val2,
        ~is_clo val1 ->
        value_of_rel env (TmCall2 val1 val2) BehErr.

  CoInductive co_value_of_rel : environment -> term -> behavior -> Prop :=
  | CoVrelConst :
      forall env n,
        co_value_of_rel env (ExpConst n) (ValNum (Z.of_nat n))
  | CoVrelDiff :
      forall env exp1 beh1 exp2 beh,
        co_value_of_rel env exp1 beh1 ->
        co_value_of_rel env (TmDiff1 beh1 exp2) beh ->
        co_value_of_rel env (ExpDiff exp1 exp2) beh
  | CoVrefDiff1_abort :
      forall beh1 env exp2,
        abort beh1 ->
        co_value_of_rel env (TmDiff1 beh1 exp2) beh1
  | CoVrelDiff1 :
      forall env exp2 beh2 val1 beh,
        co_value_of_rel env exp2 beh2 ->
        co_value_of_rel env (TmDiff2 val1 beh2) beh ->
        co_value_of_rel env (TmDiff1 val1 exp2) beh
  | CoVrelDiff2_abort :
      forall beh2 env val1,
        abort beh2 ->
        co_value_of_rel env (TmDiff2 val1 beh2) beh2
  | CoVrelDiff2 :
      forall env n1 n2,
        co_value_of_rel env (TmDiff2 (ValNum n1) (ValNum n2)) (ValNum (n1 - n2))
  | CoVrelDiff2_err :
      forall val1 val2 env,
        ~(is_num val1 /\ is_num val2) ->
        co_value_of_rel env (TmDiff2 val1 val2) BehErr
  | CoVrelIsZero :
      forall env exp1 beh1 beh,
        co_value_of_rel env exp1 beh1 ->
        co_value_of_rel env (TmIsZero1 beh1) beh ->
        co_value_of_rel env (ExpIsZero exp1) beh
  | CoVrelIsZero1_abort :
      forall beh1 env,
        abort beh1 ->
        co_value_of_rel env (TmIsZero1 beh1) beh1
  | CoVrelIsZero1 :
      forall env n1,
        co_value_of_rel env (TmIsZero1 (ValNum n1)) (ValBool (Z.eqb n1 0))
  | CoVrelIsZero1_err :
      forall val1 env,
        ~is_num val1 ->
        co_value_of_rel env (TmIsZero1 val1) BehErr
  | CoVrelIf :
      forall env exp1 beh1 exp2 exp3 beh,
        co_value_of_rel env exp1 beh1 ->
        co_value_of_rel env (TmIf1 beh1 exp2 exp3) beh ->
        co_value_of_rel env (ExpIf exp1 exp2 exp3) beh
  | CoVrelIf1_abort :
      forall beh1 env exp2 exp3,
        abort beh1 ->
        co_value_of_rel env (TmIf1 beh1 exp2 exp3) beh1
  | CoVrelIf1_true :
      forall env exp2 beh2 exp3,
        co_value_of_rel env exp2 beh2 ->
        co_value_of_rel env (TmIf1 (ValBool true) exp2 exp3) beh2
  | CoVrelIf1_false :
      forall env exp3 beh3 exp2,
        co_value_of_rel env exp3 beh3 ->
        co_value_of_rel env (TmIf1 (ValBool false) exp2 exp3) beh3
  | CoVrelIf1_err :
      forall val1 env exp2 exp3,
        ~is_bool val1 ->
        co_value_of_rel env (TmIf1 val1 exp2 exp3) BehErr
  | CoVrelVar :
      forall env x,
        co_value_of_rel env (ExpVar x) (apply_env env x)
  | CoVrelLet :
      forall env exp1 beh1 x exp2 beh,
        co_value_of_rel env exp1 beh1 ->
        co_value_of_rel env (TmLet1 x beh1 exp2) beh ->
        co_value_of_rel env (ExpLet x exp1 exp2) beh
  | CoVrelLet1_abort :
      forall beh1 env x exp2,
        abort beh1 ->
        co_value_of_rel env (TmLet1 x beh1 exp2) beh1
  | CoVrelLet1 :
      forall env x val1 exp2 beh2,
        co_value_of_rel (extend_env env x val1) exp2 beh2 ->
        co_value_of_rel env (TmLet1 x val1 exp2) beh2
  | CoVrelProc :
      forall env x exp1,
        co_value_of_rel env (ExpProc x exp1) (ValClo x exp1 env)
  | CoVrelCall :
      forall env exp1 beh1 exp2 beh,
        co_value_of_rel env exp1 beh1 ->
        co_value_of_rel env (TmCall1 beh1 exp2) beh ->
        co_value_of_rel env (ExpCall exp1 exp2) beh
  | CoVrelCall1_abort :
      forall beh1 env exp2,
        abort beh1 ->
        co_value_of_rel env (TmCall1 beh1 exp2) beh1
  | CoVrelCall1 :
      forall env exp2 beh2 val1 beh,
        co_value_of_rel env exp2 beh2 ->
        co_value_of_rel env (TmCall2 val1 beh2) beh ->
        co_value_of_rel env (TmCall1 val1 exp2) beh
  | CoVrelCall2_abort :
      forall beh2 env val1,
        abort beh2 ->
        co_value_of_rel env (TmCall2 val1 beh2) beh2
  | CoVrelCall2 :
      forall saved_env x val2 exp beh env,
        co_value_of_rel (extend_env saved_env x val2) exp beh ->
        co_value_of_rel env (TmCall2 (ValClo x exp saved_env) val2) beh
  | CoVrelCall2_err :
      forall val1 env val2,
        ~is_clo val1 ->
        co_value_of_rel env (TmCall2 val1 val2) BehErr.

  Hint Constructors expression expval environment behavior term abort is_num is_bool is_clo value_of_rel co_value_of_rel.
End ProcSpec.

Module ProcImpl.
  Export ProcSpec.

  Implicit Type exp : expression.
  Implicit Type val : expval.
  Implicit Type env : environment.
  Implicit Type beh : behavior.

  Notation "x <- e1 ; e2" :=
    (match e1 with
     | BehVal x => e2
     | BehErr => Some BehErr
     | BehDiv => Some BehDiv
     end)
      (right associativity, at level 60).

  Notation " x <-- e1 ; e2" :=
    (match e1 with
     | Some x => e2
     | None => None
     end)
      (right associativity, at level 60).

  Function value_of (fuel : nat) (env : environment) (exp : expression) : option behavior :=
    match fuel with
    | 0 => None
    | S fuel' =>
      match exp with
      | ExpConst n => Some (BehVal (ValNum (Z.of_nat n)))
      | ExpDiff exp1 exp2 =>
        beh1 <-- value_of fuel' env exp1;
          val1 <- beh1;
          beh2 <-- value_of fuel' env exp2;
          val2 <- beh2;
          match (val1, val2) with
          | (ValNum n1, ValNum n2) => Some (BehVal (ValNum (n1 - n2)))
          | _ => Some BehErr
          end
      | ExpIsZero exp1 =>
        beh1 <-- value_of fuel' env exp1;
          val1 <- beh1;
          match val1 with
          | ValNum n1 => Some (BehVal (ValBool (Z.eqb n1 0)))
          | _ => Some BehErr
          end
      | ExpIf exp1 exp2 exp3 =>
        beh1 <-- value_of fuel' env exp1;
          val1 <- beh1;
          match val1 with
          | ValBool true => value_of fuel' env exp2
          | ValBool false => value_of fuel' env exp3
          | _ => Some BehErr
          end
      | ExpVar x => Some (apply_env env x)
      | ExpLet x exp1 exp2 =>
        beh1 <-- value_of fuel' env exp1;
          val1 <- beh1; 
          value_of fuel' (extend_env env x val1) exp2
      | ExpProc x exp1 => Some (BehVal (ValClo x exp1 env))
      | ExpCall exp1 exp2 =>
        beh1 <-- value_of fuel' env exp1;
          val1 <- beh1; 
          beh2 <-- value_of fuel' env exp2;
          val2 <- beh2;
          match val1 with
          | ValClo x exp saved_env =>
            value_of fuel' (extend_env saved_env x val2) exp
          | _ => Some BehErr
          end
      end
    end.

  Hint Extern 3 => match goal with
                  | [ H : is_num (ValBool _) |- _ ] => inversion H; clear H
                  | [ H : is_num (ValClo _ _ _) |- _ ] => inversion H; clear H
                  | [ H : is_bool (ValNum _) |- _ ] => inversion H; clear H
                  | [ H : is_bool (ValClo _ _ _) |- _ ] => inversion H; clear H
                  | [ H : is_clo (ValNum _) |- _ ] => inversion H; clear H
                  | [ H : is_clo (ValBool _) |- _ ] => inversion H; clear H
                  | [ |- context[is_num (ValBool _)] ] => intuition
                  | [ |- context[is_num (ValClo _ _ _)] ] => intuition
                  | [ |- context[is_bool (ValNum _)] ] => intuition
                  | [ |- context[is_bool (ValClo _ _ _)] ] => intuition
                  | [ |- context[is_clo (ValNum _)] ] => intuition
                  | [ |- context[is_clo (ValBool _)] ] => intuition
                  | [ H : ~ _ |- _ ] => contradict H
                  end.

  Ltac invert' H := inversion H; clear H; subst.

  Theorem value_of_soundness :
    forall env exp beh,
      (exists fuel, value_of fuel env exp = Some beh) ->
      value_of_rel env exp beh.
  Proof.
    intros.
    destruct H as [ fuel ? ].
    generalize dependent env.
    generalize dependent exp.
    generalize dependent beh.
    induction fuel; intros; try discriminate; rewrite value_of_equation in *; destruct exp;
      repeat match goal with
             | [ _ : context[match value_of ?FUEL ?ENV ?EXP with Some _ => _ | None => _ end] |- _ ] =>
               destruct (value_of FUEL ENV EXP) eqn:?; try congruence
             | [ _ : context[match ?BEH with BehVal _ => _ | BehErr => _ | BehDiv => _ end] |- _ ] =>
               destruct BEH; try congruence
             | [ _ : context[match ?VAL with ValNum _ => _ | ValBool _ => _ | ValClo _ _ _ => _ end] |- _ ] =>
               destruct VAL; try congruence
             | [ _ : context[if ?B then _ else _] |- _ ] =>
               destruct B
             | [ IH : forall _, _, H : value_of _ _ _ = _ |- _ ] =>
               apply IH in H; try congruence
             | [ H : Some _ = Some _ |- _ ] =>
               invert' H
             end;
      eauto.
  Qed.

  Hint Resolve value_of_soundness.

  Definition value_of_term (fuel : nat) (env : environment) (tm : term) : option behavior :=
    match tm with
    | TmExp exp => value_of fuel env exp
    | TmDiff1 beh1 exp2 =>
      val1 <- beh1;
        beh2 <-- value_of fuel env exp2;
        val2 <- beh2;
        match (val1, val2) with
        | (ValNum n1, ValNum n2) => Some (BehVal (ValNum (n1 - n2)))
        | _ => Some BehErr
        end
    | TmDiff2 val1 beh2 =>
      val2 <- beh2;
        match (val1, val2) with
        | (ValNum n1, ValNum n2) => Some (BehVal (ValNum (n1 - n2)))
        | _ => Some BehErr
        end
    | TmIsZero1 beh1 =>
      val1 <- beh1;
        match val1 with
        | ValNum n1 => Some (BehVal (ValBool (Z.eqb n1 0)))
        | _ => Some BehErr
        end
    | TmIf1 beh1 exp2 exp3 =>
      val1 <- beh1;
        match val1 with
        | ValBool true => value_of fuel env exp2
        | ValBool false => value_of fuel env exp3
        | _ => Some BehErr
        end
    | TmLet1 x beh1 exp2 =>
      val1 <- beh1;
        value_of fuel (extend_env env x val1) exp2
    | TmCall1 beh1 exp2 =>
      val1 <- beh1;
        beh2 <-- value_of fuel env exp2;
        val2 <- beh2;
        match val1 with
        | ValClo x exp saved_env =>
          value_of fuel (extend_env saved_env x val2) exp
        | _ => Some BehErr
        end
    | TmCall2 val1 beh2 =>
      val2 <- beh2;
        match val1 with
        | ValClo x exp saved_env =>
          value_of fuel (extend_env saved_env x val2) exp
        | _ => Some BehErr
        end
    end.

  Inductive term_without_div : term -> Prop :=
  | TmNoDivExp : forall exp, term_without_div (TmExp exp)
  | TmNoDivDiff1 :
      forall beh1 exp2,
        beh1 <> BehDiv ->
        term_without_div (TmDiff1 beh1 exp2)
  | TmNoDivDiff2 :
      forall val1 beh2,
        beh2 <> BehDiv ->
        term_without_div (TmDiff2 val1 beh2)
  | TmNoDivIsZero1 :
      forall beh1,
        beh1 <> BehDiv ->
        term_without_div (TmIsZero1 beh1)
  | TmNoDivIf1 :
      forall beh1 exp2 exp3,
        beh1 <> BehDiv ->
        term_without_div (TmIf1 beh1 exp2 exp3)
  | TmNoDivLet1 :
      forall x beh1 exp2,
        beh1 <> BehDiv ->
        term_without_div (TmLet1 x beh1 exp2)
  | TmNoDivCall1 :
      forall beh1 exp2,
        beh1 <> BehDiv ->
        term_without_div (TmCall1 beh1 exp2)
  | TmNoDivCall2 :
      forall val1 beh2,
        beh2 <> BehDiv ->
        term_without_div (TmCall2 val1 beh2).

  Hint Constructors term_without_div.

  Theorem value_of_term_soundness :
    forall env tm beh,
      (exists fuel, value_of_term fuel env tm = Some beh) ->
      term_without_div tm ->
      value_of_rel env tm beh.
  Proof.
    intros; destruct tm, beh;
      repeat match goal with
             | [ H : exists _, _ |- _ ] => destruct H; simpl in *
             | [ _ : context[match ?BEH with BehVal _ => _ | BehErr => _ | BehDiv => _ end] |- _ ] =>
               destruct BEH; try congruence
             | [ _ : context[match value_of ?FUEL ?ENV ?EXP with Some _ => _ | None => _ end] |- _ ] =>
               destruct (value_of FUEL ENV EXP) eqn:?; try congruence
             | [ _ : context[match ?VAL with ValNum _ => _ | ValBool _ => _ | ValClo _ _ _ => _ end] |- _ ] =>
               destruct VAL; try congruence
             | [ _ : context[if ?B then _ else _] |- _ ] =>
               destruct B
             | [ H : Some _ = Some _ |- _ ] =>
               invert' H
             end;
      eauto 7.
  Qed.

  Hint Resolve value_of_term_soundness.

  Lemma apply_env_without_div :
    forall env x,
      apply_env env x <> BehDiv.
  Proof.
    induction env; intros; unfold apply_env.
    congruence.
    destruct (v ==v x); try congruence; auto.
  Qed.

  Hint Resolve apply_env_without_div.

  Theorem value_of_rel_wf_tm :
    forall env tm beh,
      value_of_rel env tm beh ->
      term_without_div tm ->
      beh <> BehDiv.
  Proof.
    induction 1; intros; try congruence;
    repeat match goal with
           | [ H : abort _ |- _ ] =>
             invert' H; try congruence
           | [ H : term_without_div _ |- _ ] =>
             invert' H
           end;
      eauto.
  Qed.

  Hint Resolve value_of_rel_wf_tm.

  Theorem value_of_rel_wf :
    forall env exp beh,
      value_of_rel env exp beh ->
      beh <> BehDiv.
  Proof.
    eauto.
  Qed.

  Hint Resolve value_of_rel_wf.

  Lemma fuel_incr :
    forall fuel env exp beh,
      value_of fuel env exp = Some beh ->
      value_of (S fuel) env exp = Some beh.
  Proof.
    induction fuel; intros; rewrite value_of_equation in *; subst; try congruence; destruct exp;
      repeat match goal with
             | [ _ : context[match value_of ?FUEL ?ENV ?EXP with Some _ => _ | None => _ end] |- _ ] =>
               destruct (value_of FUEL ENV EXP) eqn:?; try congruence
             | [ _ : context[match ?BEH with BehVal _ => _ | BehErr => _ | BehDiv => _ end] |- _ ] =>
               destruct BEH
             | [ _ : context[match ?VAL with ValNum _ => _ | ValBool _ => _ | ValClo _ _ _ => _ end] |- _ ] =>
               destruct VAL; try congruence
             | [ _ : context[if ?B then _ else _] |- _ ] =>
               destruct B
             | [ IH : forall _, _, H : value_of _ _ _ = _ |- _ ] =>
               apply IH in H; try congruence; rewrite H
             end;
      eauto.
  Qed.

  Hint Resolve fuel_incr.

  Lemma fuel_order :
    forall fuel env exp beh fuel',
      value_of fuel env exp = Some beh ->
      fuel <= fuel' ->
      value_of fuel' env exp = Some beh.
  Proof.
    induction 2; auto.
  Qed.

  Hint Resolve fuel_order.

  Lemma fuel_order_tm :
    forall fuel env tm beh fuel',
      value_of_term fuel env tm = Some beh ->
      fuel <= fuel' ->
      value_of_term fuel' env tm = Some beh.
  Proof.
    intros; destruct tm; simpl in *; eauto;
    repeat match goal with
           | [ _ : context[match value_of ?FUEL ?ENV ?EXP with Some _ => _ | None => _ end] |- _ ] =>
             destruct (value_of FUEL ENV EXP) eqn:T; try congruence; apply fuel_order with (fuel' := fuel') in T; eauto; rewrite T
           | [ _ : context[match ?BEH with BehVal _ => _ | BehErr => _ | BehDiv => _ end] |- _ ] =>
             destruct BEH; try congruence
           | [ _ : context[match ?VAL with ValNum _ => _ | ValBool _ => _ | ValClo _ _ _ => _ end] |- _ ] =>
             destruct VAL; try congruence
           | [ _ : context[if ?B then _ else _] |- _ ] =>
             destruct B
           end;
      eauto.
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

  Hint Resolve le_max_l le_max_r le_max_1 le_max_2 le_max_3.

  Theorem value_of_term_completeness :
    forall env tm beh,
      value_of_rel env tm beh ->
      term_without_div tm ->
      exists fuel, value_of_term fuel env tm = Some beh.
  Proof.
  Admitted.

  Theorem value_of_completeness :
    forall env exp beh,
      value_of_rel env exp beh ->
      exists fuel, value_of fuel env exp = Some beh.
  Proof.
    intros.
    apply value_of_term_completeness in H; auto.
  Qed.

  Hint Resolve value_of_completeness.

  Theorem value_of_correctness :
    forall env exp beh,
      (exists fuel, value_of fuel env exp = Some beh) <->
      value_of_rel env exp beh.
  Proof.
    intuition.
  Qed.

  Theorem value_of_completeness_with_div :
    forall env exp,
      co_value_of_rel env exp BehDiv ->
      forall fuel, value_of fuel env exp = None.
  Proof.
  Admitted.
End ProcImpl.

Export ProcImpl.