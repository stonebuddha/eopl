Require Import String.
Require Import Bool ZArith Arith List Max.
Require Import Logic.Eqdep_dec Program.Equality.
Require Import Classical.
Set Implicit Arguments.

Definition var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.
Infix "==v" := var_eq (no associativity, at level 50).

Definition loc := nat.
Definition loc_eq : forall x y : loc, {x = y} + {x <> y} := eq_nat_dec.
Infix "==l" := loc_eq (no associativity, at level 50).

Module ImplicitRefsSpec.
  Inductive expression : Set :=
  | ExpConst : nat -> expression
  | ExpDiff : expression -> expression -> expression
  | ExpIsZero : expression -> expression
  | ExpIf : expression -> expression -> expression -> expression
  | ExpVar : var -> expression
  | ExpLet : var -> expression -> expression -> expression
  | ExpProc : var -> expression -> expression
  | ExpCall : expression -> expression -> expression
  | ExpAssign : var -> expression -> expression.

  Implicit Type exp : expression.

  Inductive denval : Set :=
  | ValNum : Z -> denval
  | ValBool : bool -> denval
  | ValClo : var -> expression -> environment -> denval

  with environment : Set :=
       | EnvEmpty : environment
       | EnvExtend : var -> loc -> environment -> environment.

  Implicit Type val : denval.
  Implicit Type env : environment.

  Inductive behavior : Set :=
  | BehVal : denval -> behavior
  | BehErr : behavior.

  Implicit Type beh : behavior.

  Coercion BehVal : denval >-> behavior.

  Definition empty_env := EnvEmpty.
  Definition extend_env (env : environment) (x : var) (l : loc) := EnvExtend x l env.
  Fixpoint apply_env (env : environment) (x : var) : option loc :=
    match env with
    | EnvEmpty => None
    | EnvExtend x' l env' => if x' ==v x then Some l else apply_env env' x
    end.

  Inductive term : Set :=
  | TmExp : expression -> term
  | TmDiff1 : behavior -> expression -> term
  | TmDiff2 : denval -> behavior -> term
  | TmIsZero1 : behavior -> term
  | TmIf1 : behavior -> expression -> expression -> term
  | TmLet1 : var -> behavior -> expression -> term
  | TmCall1 : behavior -> expression -> term
  | TmCall2 : denval -> behavior -> term
  | TmAssign1 : var -> behavior -> term.

  Coercion TmExp : expression >-> term.

  Inductive abort : behavior -> Prop :=
  | AbrErr : abort BehErr.

  Inductive is_num : denval -> Prop :=
  | IsNum : forall n, is_num (ValNum n).

  Inductive is_bool : denval -> Prop :=
  | IsBool : forall b, is_bool (ValBool b).

  Inductive is_clo : denval -> Prop :=
  | IsClo : forall x exp1 saved_env, is_clo (ValClo x exp1 saved_env).

  Definition store := list denval.
  Definition empty_store : store := nil.
  Definition newref_store (st : store) (val : denval) : store * loc :=
    let l := length st in
    (app st (cons val nil), l).
  Definition deref_store (st : store) (l : loc) : behavior :=
    match nth_error st l with
    | Some val => val
    | None => BehErr
    end.
  Definition setref_store (st : store) (l : loc) (val : denval) : option store :=
    let inner :=
        fix f (st : store) (l : loc) : option store :=
          match st with
          | nil => None
          | val' :: st' =>
            match l with
            | O => Some (val :: st')
            | S l' =>
              match f st' l' with
              | Some st' => Some (val' :: st')
              | None => None
              end
            end
          end in
    inner st l.

  Inductive value_of_rel : environment -> term -> behavior -> store -> store -> Prop :=
  | VrelConst :
      forall env n st,
        value_of_rel env (ExpConst n) (ValNum (Z.of_nat n)) st st
  | VrelDiff :
      forall env exp1 beh1 st0 st1 exp2 beh st2,
        value_of_rel env exp1 beh1 st0 st1 ->
        value_of_rel env (TmDiff1 beh1 exp2) beh st1 st2 ->
        value_of_rel env (ExpDiff exp1 exp2) beh st0 st2
  | VrefDiff1_abort :
      forall beh1 env exp2 st,
        abort beh1 ->
        value_of_rel env (TmDiff1 beh1 exp2) beh1 st st
  | VrelDiff1 :
      forall env exp2 beh2 st0 st1 val1 beh st2,
        value_of_rel env exp2 beh2 st0 st1 ->
        value_of_rel env (TmDiff2 val1 beh2) beh st1 st2 ->
        value_of_rel env (TmDiff1 val1 exp2) beh st0 st2
  | VrelDiff2_abort :
      forall beh2 env val1 st,
        abort beh2 ->
        value_of_rel env (TmDiff2 val1 beh2) beh2 st st
  | VrelDiff2 :
      forall env n1 n2 st,
        value_of_rel env (TmDiff2 (ValNum n1) (ValNum n2)) (ValNum (n1 - n2)) st st
  | VrelDiff2_err :
      forall val1 val2 env st,
        ~(is_num val1 /\ is_num val2) ->
        value_of_rel env (TmDiff2 val1 val2) BehErr st st
  | VrelIsZero :
      forall env exp1 beh1 st0 st1 beh st2,
        value_of_rel env exp1 beh1 st0 st1 ->
        value_of_rel env (TmIsZero1 beh1) beh st1 st2 ->
        value_of_rel env (ExpIsZero exp1) beh st0 st2
  | VrelIsZero1_abort :
      forall beh1 env st,
        abort beh1 ->
        value_of_rel env (TmIsZero1 beh1) beh1 st st
  | VrelIsZero1 :
      forall env n1 st,
        value_of_rel env (TmIsZero1 (ValNum n1)) (ValBool (Z.eqb n1 0)) st st
  | VrelIsZero1_err :
      forall val1 env st,
        ~is_num val1 ->
        value_of_rel env (TmIsZero1 val1) BehErr st st
  | VrelIf :
      forall env exp1 beh1 st0 st1 exp2 exp3 beh st2,
        value_of_rel env exp1 beh1 st0 st1 ->
        value_of_rel env (TmIf1 beh1 exp2 exp3) beh st1 st2 ->
        value_of_rel env (ExpIf exp1 exp2 exp3) beh st0 st2
  | VrelIf1_abort :
      forall beh1 env exp2 exp3 st,
        abort beh1 ->
        value_of_rel env (TmIf1 beh1 exp2 exp3) beh1 st st
  | VrelIf1_true :
      forall env exp2 beh2 st0 st1 exp3,
        value_of_rel env exp2 beh2 st0 st1 ->
        value_of_rel env (TmIf1 (ValBool true) exp2 exp3) beh2 st0 st1
  | VrelIf1_false :
      forall env exp3 beh3 st0 st1 exp2,
        value_of_rel env exp3 beh3 st0 st1 ->
        value_of_rel env (TmIf1 (ValBool false) exp2 exp3) beh3 st0 st1
  | VrelIf1_err :
      forall val1 env exp2 exp3 st,
        ~is_bool val1 ->
        value_of_rel env (TmIf1 val1 exp2 exp3) BehErr st st
  | VrelVar :
      forall env x l st,
        apply_env env x = Some l ->
        value_of_rel env (ExpVar x) (deref_store st l) st st
  | VrelVar_err :
      forall env x st,
        apply_env env x = None ->
        value_of_rel env (ExpVar x) BehErr st st
  | VrelLet :
      forall env exp1 beh1 st0 st1 x exp2 beh st2,
        value_of_rel env exp1 beh1 st0 st1->
        value_of_rel env (TmLet1 x beh1 exp2) beh st1 st2 ->
        value_of_rel env (ExpLet x exp1 exp2) beh st0 st2
  | VrelLet1_abort :
      forall beh1 env x exp2 st,
        abort beh1 ->
        value_of_rel env (TmLet1 x beh1 exp2) beh1 st st
  | VrelLet1 :
      forall st0 val1 st1 l env x exp2 beh2 st2,
        newref_store st0 val1 = (st1, l) ->
        value_of_rel (extend_env env x l) exp2 beh2 st1 st2 ->
        value_of_rel env (TmLet1 x val1 exp2) beh2 st0 st2
  | VrelProc :
      forall env x exp1 st,
        value_of_rel env (ExpProc x exp1) (ValClo x exp1 env) st st
  | VrelCall :
      forall env exp1 beh1 st0 st1 exp2 beh st2,
        value_of_rel env exp1 beh1 st0 st1 ->
        value_of_rel env (TmCall1 beh1 exp2) beh st1 st2 ->
        value_of_rel env (ExpCall exp1 exp2) beh st0 st2
  | VrelCall1_abort :
      forall beh1 env exp2 st,
        abort beh1 ->
        value_of_rel env (TmCall1 beh1 exp2) beh1 st st
  | VrelCall1 :
      forall env exp2 beh2 st0 st1 val1 beh st2,
        value_of_rel env exp2 beh2 st0 st1 ->
        value_of_rel env (TmCall2 val1 beh2) beh st1 st2 ->
        value_of_rel env (TmCall1 val1 exp2) beh st0 st2
  | VrelCall2_abort :
      forall beh2 env val1 st,
        abort beh2 ->
        value_of_rel env (TmCall2 val1 beh2) beh2 st st
  | VrelCall2 :
      forall st0 val2 st1 l saved_env x exp1 beh st2 env,
        newref_store st0 val2 = (st1, l) ->
        value_of_rel (extend_env saved_env x l) exp1 beh st1 st2 ->
        value_of_rel env (TmCall2 (ValClo x exp1 saved_env) val2) beh st0 st2
  | VrelCall2_err :
      forall val1 env val2 st,
        ~is_clo val1 ->
        value_of_rel env (TmCall2 val1 val2) BehErr st st
  | VrelAssign :
      forall env exp1 beh1 st0 st1 x beh st2,
        value_of_rel env exp1 beh1 st0 st1 ->
        value_of_rel env (TmAssign1 x beh1) beh st1 st2 ->
        value_of_rel env (ExpAssign x exp1) beh st0 st2
  | VrelAssign1_abort :
      forall beh1 env x st,
        abort beh1 ->
        value_of_rel env (TmAssign1 x beh1) beh1 st st
  | VrelAssign1 :
      forall env x l st0 val1 st1,
        apply_env env x = Some l ->
        setref_store st0 l val1 = Some st1 ->
        value_of_rel env (TmAssign1 x val1) (BehVal (ValNum 27)) st0 st1
  | VrelAssign1_err1 :
      forall env x val1 st,
        apply_env env x = None ->
        value_of_rel env (TmAssign1 x val1) BehErr st st
  | VrelAssign1_err2 :
      forall env x l st val1,
        apply_env env x = Some l ->
        setref_store st l val1 = None ->
        value_of_rel env (TmAssign1 x val1) BehErr st st.

  Hint Constructors expression denval environment behavior term abort is_num is_bool is_clo value_of_rel.
End ImplicitRefsSpec.

Module ImplicitRefsImpl.
  Export ImplicitRefsSpec.

  Implicit Type exp : expression.
  Implicit Type val : denval.
  Implicit Type env : environment.
  Implicit Type beh : behavior.

  Notation "x <-- e1 ; e2" :=
    (match e1 with
     | Some x => e2
     | None => None
     end)
      (right associativity, at level 60).

  Function value_of (fuel : nat) (env : environment) (exp : expression) (st : store) : option (behavior * store) :=
    match fuel with
    | O => None
    | S fuel' =>
      match exp with
      | ExpConst n => Some (BehVal (ValNum (Z.of_nat n)), st)
      | ExpDiff exp1 exp2 =>
        res1 <-- value_of fuel' env exp1 st;
          let (beh1, st1) := res1 in
          match beh1 with
          | BehVal val1 =>
            res2 <-- value_of fuel' env exp2 st1;
              let (beh2, st2) := res2 in
              match beh2 with
              | BehVal val2 =>
                match (val1, val2) with
                | (ValNum n1, ValNum n2) => Some (BehVal (ValNum (n1 - n2)), st2)
                | _ => Some (BehErr, st2)
                end
              | BehErr => Some (BehErr, st2)
              end
          | BehErr => Some (BehErr, st1)
          end
      | ExpIsZero exp1 =>
        res1 <-- value_of fuel' env exp1 st;
          let (beh1, st1) := res1 in
          match beh1 with
          | BehVal val1 =>
            match val1 with
            | ValNum n1 => Some (BehVal (ValBool (Z.eqb n1 0)), st1)
            | _ => Some (BehErr, st1)
            end
          | BehErr => Some (BehErr, st1)
          end
      | ExpIf exp1 exp2 exp3 =>
        res1 <-- value_of fuel' env exp1 st;
          let (beh1, st1) := res1 in
          match beh1 with
          | BehVal val1 =>
            match val1 with
            | ValBool true => value_of fuel' env exp2 st1
            | ValBool false => value_of fuel' env exp3 st1
            | _ => Some (BehErr, st1)
            end
          | BehErr => Some (BehErr, st1)
          end
      | ExpVar x =>
        match apply_env env x with
        | Some l => Some (deref_store st l, st)
        | None => Some (BehErr, st)
        end
      | ExpLet x exp1 exp2 =>
        res1 <-- value_of fuel' env exp1 st;
          let (beh1, st1) := res1 in
          match beh1 with
          | BehVal val1 =>
            let (st2, l) := newref_store st1 val1 in
            value_of fuel' (extend_env env x l) exp2 st2
          | BehErr => Some (BehErr, st1)
          end
      | ExpProc x exp1 => Some (BehVal (ValClo x exp1 env), st)
      | ExpCall exp1 exp2 =>
        res1 <-- value_of fuel' env exp1 st;
          let (beh1, st1) := res1 in
          match beh1 with
          | BehVal val1 =>
            res2 <-- value_of fuel' env exp2 st1;
              let (beh2, st2) := res2 in
              match beh2 with
              | BehVal val2 =>
                match val1 with
                | ValClo x exp saved_env =>
                  let (st3, l) := newref_store st2 val2 in
                  value_of fuel' (extend_env saved_env x l) exp st3
                | _ => Some (BehErr, st2)
                end
              | BehErr => Some (BehErr, st2)
              end
          | BehErr => Some (BehErr, st1)
          end
      | ExpAssign x exp1 =>
        res1 <-- value_of fuel' env exp1 st;
          let (beh1, st1) := res1 in
          match beh1 with
          | BehVal val1 =>
            match apply_env env x with
            | Some l =>
              match setref_store st1 l val1 with
              | Some st2 => Some (BehVal (ValNum 27), st2)
              | None => Some (BehErr, st1)
              end
            | None => Some (BehErr, st1)
            end
          | BehErr => Some (BehErr, st1)
          end
      end
    end.

  Ltac invert' H := inversion H; clear H; subst.

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

  Theorem value_of_soundness :
    forall env exp st0 beh st1,
      (exists fuel, value_of fuel env exp st0 = Some (beh, st1)) ->
      value_of_rel env exp beh st0 st1.
  Proof.
    intros.
    destruct H as [ fuel ? ].
    generalize dependent env.
    generalize dependent exp.
    generalize dependent st0.
    generalize dependent beh.
    generalize dependent st1.
    induction fuel; intros; try discriminate; rewrite value_of_equation in *; destruct exp, beh;
      repeat match goal with
             | [ _ : context[match value_of ?FUEL ?ENV ?EXP ?ST with Some _ => _ | None => _ end] |- _ ] =>
               destruct (value_of FUEL ENV EXP ST) eqn:?; try congruence
             | [ _ : context[match setref_store ?ST ?L ?VAL with Some _ => _ | None => _ end] |- _ ] =>
               destruct (setref_store ST L VAL) eqn:?; try congruence
             | [ _ : context[match apply_env ?ENV ?VAR with Some _ => _ | None => _ end] |- _ ] =>
               destruct (apply_env ENV VAR) eqn:?; try congruence
             | [ _ : context[let (_, _) := ?RES in _] |- _ ] =>
               destruct RES eqn:?
             | [ _ : context[match ?BEH with BehVal _ => _ | BehErr => _ end] |- _ ] =>
               destruct BEH; try congruence
             | [ _ : context[match ?VAL with ValNum _ => _ | ValBool _ => _ | ValClo _ _ _ => _ end] |- _ ] =>
               destruct VAL; try congruence
             | [ _ : context[if ?B then _ else _] |- _ ] =>
               destruct B
             | [ IH : forall _, _, H : value_of _ _ _ _ = _ |- _ ] =>
               apply IH in H; try congruence
             | [ H : Some _ = Some _ |- _ ] =>
               invert' H
             end;
      eauto.
  Qed.

  Definition value_of_term (fuel : nat) (env : environment) (tm : term) (st : store) : option (behavior * store) :=
    match tm with
    | TmExp exp => value_of fuel env exp st
    | TmDiff1 beh1 exp2 =>
      match beh1 with
      | BehVal val1 =>
        res2 <-- value_of fuel env exp2 st;
          let (beh2, st2) := res2 in
          match beh2 with
          | BehVal val2 =>
            match (val1, val2) with
            | (ValNum n1, ValNum n2) => Some (BehVal (ValNum (n1 - n2)), st2)
            | _ => Some (BehErr, st2)
            end
          | BehErr => Some (BehErr, st2)
          end
      | BehErr => Some (BehErr, st)
      end
    | TmDiff2 val1 beh2 =>
      match beh2 with
      | BehVal val2 =>
        match (val1, val2) with
        | (ValNum n1, ValNum n2) => Some (BehVal (ValNum (n1 - n2)), st)
        | _ => Some (BehErr, st)
        end
      | BehErr => Some (BehErr, st)
      end
    | TmIsZero1 beh1 =>
      match beh1 with
      | BehVal val1 =>
        match val1 with
        | ValNum n1 => Some (BehVal (ValBool (Z.eqb n1 0)), st)
        | _ => Some (BehErr, st)
        end
      | BehErr => Some (BehErr, st)
      end
    | TmIf1 beh1 exp2 exp3 =>
      match beh1 with
      | BehVal val1 =>
        match val1 with
        | ValBool true => value_of fuel env exp2 st
        | ValBool false => value_of fuel env exp3 st
        | _ => Some (BehErr, st)
        end
      | BehErr => Some (BehErr, st)
      end
    | TmLet1 x beh1 exp2 =>
      match beh1 with
      | BehVal val1 =>
        let (st1, l) := newref_store st val1 in
        value_of fuel (extend_env env x l) exp2 st1
      | BehErr => Some (BehErr, st)
      end
    | TmCall1 beh1 exp2 =>
      match beh1 with
      | BehVal val1 =>
        res2 <-- value_of fuel env exp2 st;
          let (beh2, st2) := res2 in
          match beh2 with
          | BehVal val2 =>
            match val1 with
            | ValClo x exp saved_env =>
              let (st3, l) := newref_store st2 val2 in
              value_of fuel (extend_env saved_env x l) exp st3
            | _ => Some (BehErr, st2)
            end
          | BehErr => Some (BehErr, st2)
          end
      | BehErr => Some (BehErr, st)
      end
    | TmCall2 val1 beh2 =>
      match beh2 with
      | BehVal val2 =>
        match val1 with
        | ValClo x exp saved_env =>
          let (st1, l) := newref_store st val2 in
          value_of fuel (extend_env saved_env x l) exp st1
        | _ => Some (BehErr, st)
        end
      | BehErr => Some (BehErr, st)
      end
    | TmAssign1 x beh1 =>
      match beh1 with
      | BehVal val1 =>
        match apply_env env x with
        | Some l =>
          match setref_store st l val1 with
          | Some st1 => Some (BehVal (ValNum 27), st1)
          | None => Some (BehErr, st)
          end
        | None => Some (BehErr, st)
        end
      | BehErr => Some (BehErr, st)
      end
    end.

  Lemma fuel_incr :
    forall fuel env exp st0 beh st1,
      value_of fuel env exp st0 = Some (beh, st1) ->
      value_of (S fuel) env exp st0 = Some (beh, st1).
  Proof.
    induction fuel; intros; try discriminate; rewrite value_of_equation in *; destruct exp, beh;
      repeat match goal with
             | [ _ : context[match value_of ?FUEL ?ENV ?EXP ?ST with Some _ => _ | None => _ end] |- _ ] =>
               destruct (value_of FUEL ENV EXP ST) eqn:?; try congruence
             | [ _ : context[let (_, _) := ?RES in _] |- _ ] =>
               destruct RES eqn:?
             | [ _ : context[match ?BEH with BehVal _ => _ | BehErr => _ end] |- _ ] =>
               destruct BEH; try congruence
             | [ _ : context[match ?VAL with ValNum _ => _ | ValBool _ => _ | ValClo _ _ _ => _ end] |- _ ] =>
               destruct VAL; try congruence
             | [ _ : context[if ?B then _ else _] |- _ ] =>
               destruct B
             | [ IH : forall _, _, H : value_of _ _ _ _ = _ |- _ ] =>
               apply IH in H; try congruence; rewrite H
             | [ |- context[let (_, _) := ?RES in _] ] =>
               destruct RES
             | [ H : (_, _) = (_, _) |- _ ] =>
               invert' H
             end;
      eauto.
  Qed.

  Hint Resolve fuel_incr.

  Lemma fuel_order :
    forall fuel env exp st0 beh st1 fuel',
      value_of fuel env exp st0 = Some (beh, st1) ->
      fuel <= fuel' ->
      value_of fuel' env exp st0 = Some (beh, st1).
  Proof.
    induction 2; auto.
  Qed.

  Lemma fuel_order_tm :
    forall fuel env tm st0 beh st1 fuel',
      value_of_term fuel env tm st0 = Some (beh, st1) ->
      fuel <= fuel' ->
      value_of_term fuel' env tm st0 = Some (beh, st1).
  Proof.
    intros; destruct tm, beh; simpl in *;
      repeat match goal with
             | [ _ : context[match value_of ?FUEL ?ENV ?EXP ?ST with Some _ => _ | None => _ end] |- _ ] =>
               destruct (value_of FUEL ENV EXP ST) eqn:?; try congruence
             | [ _ : context[let (_, _) := ?RES in _] |- _ ] =>
               destruct RES eqn:?
             | [ H : value_of ?FUEL ?ENV ?EXP ?ST = _ |- _ ] =>
               apply fuel_order with (fuel' := fuel') in H; eauto; rewrite H; clear H
             | [ _ : context[match ?BEH with BehVal _ => _ | BehErr => _ end] |- _ ] =>
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
    forall env tm beh st0 st1,
      value_of_rel env tm beh st0 st1 ->
      exists fuel, value_of_term fuel env tm st0 = Some (beh, st1).
  Proof.
    induction 1; auto;
      match goal with
      | [ IH1 : exists _, _, IH2 : exists _, _ |- _ ] =>
        destruct IH1 as [ fuel1 ? ]; destruct IH2 as [ fuel2 ? ]; exists (S (max fuel1 fuel2))
      | [ IH1 : exists _, _ |- _ ] =>
        destruct IH1 as [ fuel1 ? ]; exists (S fuel1)
      | [ |- _ ] =>
        exists 1
      end;
      unfold value_of_term in *;
      try match goal with
      | [ |- value_of _ _ _ _ = _ ] => rewrite value_of_equation
      end;
      repeat match goal with
             | [ _ : context[match value_of ?FUEL ?ENV ?EXP ?ST with Some _ => _ | None => _ end] |- _ ] =>
               destruct (value_of FUEL ENV EXP ST) eqn:?; try congruence
             | [ _ : context[let (_, _) := ?RES in _] |- _ ] =>
               destruct RES eqn:?
             | [ _ : context[match ?VAL with ValNum _ => _ | ValBool _ => _ | ValClo _ _ _ => _ end] |- _ ] =>
               destruct VAL; try congruence
             | [ _ : context[match ?BEH with BehVal _ => _ | BehErr => _ end] |- _ ] =>
               destruct BEH; try congruence
             | [ _ : context[if ?B then _ else _] |- _ ] =>
               destruct B
             | [ H : value_of ?FUEL1 ?ENV ?EXP ?ST = _ |- context[value_of ?FUEL2 ?ENV ?EXP ?ST] ] =>
               apply fuel_order with (fuel' := FUEL2) in H; eauto; rewrite H; clear H
             | [ |- match ?VAL with ValNum _ => _ | ValBool _ => _ | ValClo _ _ _ => _ end = _ ] =>
               destruct VAL; try congruence
             | [ |- context[match apply_env ?ENV ?VAR with Some _ => _ | None => _ end] ] =>
               destruct (apply_env ENV VAR) eqn:?; try congruence
             | [ |- context[match setref_store ?ST ?L ?VAL with Some _ => _ | None => _ end] ] =>
               destruct (setref_store ST L VAL) eqn:?; try congruence
             | [ |- context[let (_, _) := newref_store ?ST ?VAL in _] ] =>
               destruct (newref_store ST VAL) eqn:?; try congruence
             | [ H : setref_store _ _ _ = _ |- _ ] =>
               try (rewrite H; clear H)
             | [ H : abort _ |- _ ] =>
               invert' H
             | [ H : (_, _) = (_, _) |- _ ] =>
               invert' H
             end;
      eauto.
  Qed.

  Theorem value_of_completeness :
    forall env exp beh st0 st1,
      value_of_rel env exp beh st0 st1 ->
      exists fuel, value_of fuel env exp st0 = Some (beh, st1).
  Proof.
    intros.
    apply value_of_term_completeness in H; auto.
  Qed.

  Hint Resolve value_of_soundness value_of_completeness.

  Theorem value_of_correctness :
    forall env exp st0 beh st1,
      (exists fuel, value_of fuel env exp st0 = Some (beh, st1)) <->
      value_of_rel env exp beh st0 st1.
  Proof.
    intuition.
  Qed.
End ImplicitRefsImpl.

Export ImplicitRefsImpl.