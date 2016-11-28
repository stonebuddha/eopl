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

Module ExplicitRefsSpec.
  Inductive expression : Set :=
  | ExpConst : nat -> expression
  | ExpDiff : expression -> expression -> expression
  | ExpIsZero : expression -> expression
  | ExpIf : expression -> expression -> expression -> expression
  | ExpVar : var -> expression
  | ExpLet : var -> expression -> expression -> expression
  | ExpProc : var -> expression -> expression
  | ExpCall : expression -> expression -> expression
  | ExpNewref : expression -> expression
  | ExpDeref : expression -> expression
  | ExpSetref : expression -> expression -> expression.

  Implicit Type exp : expression.

  Inductive expval : Set :=
  | ValNum : Z -> expval
  | ValBool : bool -> expval
  | ValClo : var -> expression -> environment -> expval
  | ValRef : loc -> expval

  with environment : Set :=
       | EnvEmpty : environment
       | EnvExtend : var -> expval -> environment -> environment.

  Implicit Type val : expval.
  Implicit Type env : environment.

  Inductive behavior : Set :=
  | BehVal : expval -> behavior
  | BehErr : behavior.

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
  | TmCall2 : expval -> behavior -> term
  | TmNewref1 : behavior -> term
  | TmDeref1 : behavior -> term
  | TmSetref1 : behavior -> expression -> term
  | TmSetref2 : expval -> behavior -> term.

  Coercion TmExp : expression >-> term.

  Inductive abort : behavior -> Prop :=
  | AbrErr : abort BehErr.

  Inductive is_num : expval -> Prop :=
  | IsNum : forall n, is_num (ValNum n).

  Inductive is_bool : expval -> Prop :=
  | IsBool : forall b, is_bool (ValBool b).

  Inductive is_clo : expval -> Prop :=
  | IsClo : forall x exp1 saved_env, is_clo (ValClo x exp1 saved_env).

  Inductive is_ref : expval -> Prop :=
  | IsRef : forall l, is_ref (ValRef l).

  Definition store := list expval.
  Definition empty_store : store := nil.
  Definition newref_store (st : store) (val : expval) : store * loc :=
    let l := length st in
    (app st (cons val nil), l).
  Definition deref_store (st : store) (l : loc) : behavior :=
    match nth_error st l with
    | Some val => val
    | None => BehErr
    end.
  Definition setref_store (st : store) (l : loc) (val : expval) : option store :=
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

  Lemma deref_empty : forall l, deref_store empty_store l = BehErr.
    intros; unfold deref_store, empty_store.
    destruct l; simpl in *; eauto.
  Qed.

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
      forall env x st,
        value_of_rel env (ExpVar x) (apply_env env x) st st
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
      forall env x val1 exp2 beh2 st0 st1,
        value_of_rel (extend_env env x val1) exp2 beh2 st0 st1 ->
        value_of_rel env (TmLet1 x val1 exp2) beh2 st0 st1
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
      forall saved_env x val2 exp1 beh st0 st1 env,
        value_of_rel (extend_env saved_env x val2) exp1 beh st0 st1 ->
        value_of_rel env (TmCall2 (ValClo x exp1 saved_env) val2) beh st0 st1
  | VrelCall2_err :
      forall val1 env val2 st,
        ~is_clo val1 ->
        value_of_rel env (TmCall2 val1 val2) BehErr st st
  | VrelNewref :
      forall env exp1 beh1 st0 st1 beh st2,
        value_of_rel env exp1 beh1 st0 st1 ->
        value_of_rel env (TmNewref1 beh1) beh st1 st2 ->
        value_of_rel env (ExpNewref exp1) beh st0 st2
  | VrelNewref1_abort :
      forall beh1 env st,
        abort beh1 ->
        value_of_rel env (TmNewref1 beh1) beh1 st st
  | VrelNewref1 :
      forall st0 val1 st1 l env,
        newref_store st0 val1 = (st1, l) ->
        value_of_rel env (TmNewref1 val1) (ValRef l) st0 st1
  | VrelDeref :
      forall env exp1 beh1 st0 st1 beh st2,
        value_of_rel env exp1 beh1 st0 st1 ->
        value_of_rel env (TmDeref1 beh1) beh st1 st2 ->
        value_of_rel env (ExpDeref exp1) beh st0 st2
  | VrelDeref1_abort :
      forall beh1 env st,
        abort beh1 ->
        value_of_rel env (TmDeref1 beh1) beh1 st st
  | VrelDeref1 :
      forall env l st,
        value_of_rel env (TmDeref1 (ValRef l)) (deref_store st l) st st
  | VrelSetref :
      forall env exp1 beh1 st0 st1 exp2 beh st2,
        value_of_rel env exp1 beh1 st0 st1 ->
        value_of_rel env (TmSetref1 beh1 exp2) beh st1 st2 ->
        value_of_rel env (ExpSetref exp1 exp2) beh st0 st2
  | VrelSetref1_abort :
      forall beh1 env exp2 st,
        abort beh1 ->
        value_of_rel env (TmSetref1 beh1 exp2) beh1 st st
  | VrelSetref1 :
      forall env exp2 beh2 st0 st1 val1 beh st2,
        value_of_rel env exp2 beh2 st0 st1 ->
        value_of_rel env (TmSetref2 val1 beh2) beh st1 st2 ->
        value_of_rel env (TmSetref1 val1 exp2) beh st0 st2
  | VrelSetref2_abort :
      forall beh2 env val1 st,
        abort beh2 ->
        value_of_rel env (TmSetref2 val1 beh2) beh2 st st
  | VrelSetref2 :
      forall st0 l val st1 env,
        setref_store st0 l val = Some st1 ->
        value_of_rel env (TmSetref2 (ValRef l) val) (ValNum 23) st0 st1
  | VrelSetref2_err1 :
      forall val1 env val2 st,
        ~is_ref val1 ->
        value_of_rel env (TmSetref2 val1 val2) BehErr st st
  | VrelSetref2_err2 :
      forall st l val env,
        setref_store st l val = None ->
        value_of_rel env (TmSetref2 (ValRef l) val) BehErr st st.

  Hint Constructors expression expval environment behavior term abort is_num is_bool is_clo is_ref value_of_rel.
End ExplicitRefsSpec.

Module ExplicitRefsImpl.
  Export ExplicitRefsSpec.

  Implicit Type exp : expression.
  Implicit Type val : expval.
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
            res2 <-- value_of fuel' env exp2 st;
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
      | ExpVar x => Some (apply_env env x, st)
      | ExpLet x exp1 exp2 =>
        res1 <-- value_of fuel' env exp1 st;
          let (beh1, st1) := res1 in
          match beh1 with
          | BehVal val1 =>
            value_of fuel' (extend_env env x val1) exp2 st1
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
                  value_of fuel' (extend_env saved_env x val2) exp st2
                | _ => Some (BehErr, st2)
                end
              | BehErr => Some (BehErr, st2)
              end
          | BehErr => Some (BehErr, st1)
          end
      | ExpNewref exp1 =>
        res1 <-- value_of fuel' env exp1 st;
          let (beh1, st1) := res1 in
          match beh1 with
          | BehVal val1 =>
            let (st2, l) := newref_store st1 val1 in
            Some (BehVal (ValRef l), st2)
          | BehErr => Some (BehErr, st1)
          end
      | ExpDeref exp1 =>
        res1 <-- value_of fuel' env exp1 st;
          let (beh1, st1) := res1 in
          match beh1 with
          | BehVal val1 =>
            match val1 with
            | ValRef l => Some (deref_store st1 l, st1)
            | _ => Some (BehErr, st1)
            end
          | BehErr => Some (BehErr, st1)
          end
      | ExpSetref exp1 exp2 =>
        res1 <-- value_of fuel' env exp1 st;
          let (beh1, st1) := res1 in
          match beh1 with
          | BehVal val1 =>
            res2 <-- value_of fuel' env exp2 st1;
              let (beh2, st2) := res2 in
              match beh2 with
              | BehVal val2 =>
                match val1 with
                | ValRef l =>
                  match setref_store st2 l val2 with
                  | Some st3 => Some (BehVal (ValNum 23), st3)
                  | None => Some (BehErr, st2)
                  end
                | _ => Some (BehErr, st2)
                end
              | BehErr => Some (BehErr, st2)
              end
          | BehErr => Some (BehErr, st1)
          end
      end
    end.

  Ltac invert' H := inversion H; clear H; subst.

  Theorem value_of_soundness :
    forall env exp st0 beh st1,
      (exists fuel, value_of fuel env exp st0 = Some (beh, st1)) ->
      value_of_rel env exp beh st0 st1.
  Proof.
  Admitted.

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
        value_of fuel (extend_env env x val1) exp2 st
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
              value_of fuel (extend_env saved_env x val2) exp st2
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
          value_of fuel (extend_env saved_env x val2) exp st
        | _ => Some (BehErr, st)
        end
      | BehErr => Some (BehErr, st)
      end
    | TmNewref1 beh1 =>
      match beh1 with
      | BehVal val1 =>
        let (st2, l) := newref_store st val1 in
        Some (BehVal (ValRef l), st2)
      | BehErr => Some (BehErr, st)
      end
    | TmDeref1 beh1 =>
      match beh1 with
      | BehVal val1 =>
        match val1 with
        | ValRef l => Some (deref_store st l, st)
        | _ => Some (BehErr, st)
        end
      | BehErr => Some (BehErr, st)
      end
    | TmSetref1 beh1 exp2 =>
      match beh1 with
      | BehVal val1 =>
        res2 <-- value_of fuel env exp2 st;
          let (beh2, st2) := res2 in
          match beh2 with
          | BehVal val2 =>
            match val1 with
            | ValRef l =>
              match setref_store st2 l val2 with
              | Some st3 => Some (BehVal (ValNum 23), st3)
              | None => Some (BehErr, st2)
              end
            | _ => Some (BehErr, st2)
            end
          | BehErr => Some (BehErr, st2)
          end
      | BehErr => Some (BehErr, st)
      end
    | TmSetref2 val1 beh2 =>
      match beh2 with
      | BehVal val2 =>
        match val1 with
        | ValRef l =>
          match setref_store st l val2 with
          | Some st3 => Some (BehVal (ValNum 23), st3)
          | None => Some (BehErr, st)
          end
        | _ => Some (BehErr, st)
        end
      | BehErr => Some (BehErr, st)
      end
    end.

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
  Admitted.

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
End ExplicitRefsImpl.

Export ExplicitRefsImpl.