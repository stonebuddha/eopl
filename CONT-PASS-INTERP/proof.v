Require Import Bool ZArith Arith List Max.
Require Import String.
Set Implicit Arguments.

Definition var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.
Infix "==v" := var_eq (no associativity, at level 50).

Module LetrecSpec.
  Inductive expression : Set :=
  | ExpConst : nat -> expression
  | ExpDiff : expression -> expression -> expression
  | ExpIsZero : expression -> expression
  | ExpIf : expression -> expression -> expression -> expression
  | ExpVar : var -> expression
  | ExpLet : var -> expression -> expression -> expression
  | ExpProc : var -> expression -> expression
  | ExpCall : expression -> expression -> expression
  | ExpLetrec : var -> var -> expression -> expression -> expression.

  Implicit Type exp : expression.

  Inductive expval : Set :=
  | ValNum : Z -> expval
  | ValBool : bool -> expval
  | ValClo : var -> expression -> environment -> expval

  with environment : Set :=
       | EnvEmpty : environment
       | EnvExtend : var -> expval -> environment -> environment
       | EnvExtendRec : var -> var -> expression -> environment -> environment.

  Implicit Type val : expval.
  Implicit Type env : environment.

  Inductive behavior : Set :=
  | BehVal : expval -> behavior
  | BehErr : behavior.

  Implicit Type beh : behavior.

  Coercion BehVal : expval >-> behavior.

  Definition empty_env := EnvEmpty.
  Definition extend_env (env : environment) (x : var) (v : expval) : environment := EnvExtend x v env.
  Definition extend_env_rec (env : environment) (p_name : var) (b_var : var) (p_body : expression) : environment := EnvExtendRec p_name b_var p_body env.
  Fixpoint apply_env (env : environment) (x : var) : behavior :=
    match env with
    | EnvEmpty => BehErr
    | EnvExtend x' v env' => if x' ==v x then v else apply_env env' x
    | EnvExtendRec p_name b_var p_body env' => if p_name ==v x then ValClo b_var p_body env else apply_env env' x
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
  | AbrErr : abort BehErr.

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
        value_of_rel env (TmCall2 val1 val2) BehErr
  | VrelLetrec :
      forall env p_name b_var p_body exp1 beh,
        value_of_rel (extend_env_rec env p_name b_var p_body) exp1 beh ->
        value_of_rel env (ExpLetrec p_name b_var p_body exp1) beh.
  
  Hint Constructors expression expval environment behavior term abort is_num is_bool is_clo value_of_rel.
End LetrecSpec.
  
Module LetrecImpl.
  Export LetrecSpec.

  Implicit Type exp : expression.
  Implicit Type val : expval.
  Implicit Type env : environment.
  Implicit Type beh : behavior.

  Inductive continuation : Set :=
  | ContEnd : continuation
  | ContDiff1 : expression -> environment -> continuation -> continuation
  | ContDiff2 : expval -> continuation -> continuation
  | ContIsZero : continuation -> continuation
  | ContIf : expression -> expression -> environment -> continuation -> continuation
  | ContLet : var -> expression -> environment -> continuation -> continuation
  | ContCall1 : expression -> environment -> continuation -> continuation
  | ContCall2 : expval -> continuation -> continuation.

  Implicit Type cont : continuation.

  Notation "x <- e1 ; e2" :=
    (match e1 with
     | BehVal x => e2
     | BehErr => Some BehErr
     end)
      (right associativity, at level 60).

  Notation " x <-- e1 ; e2" :=
    (match e1 with
     | Some x => e2
     | None => None
     end)
      (right associativity, at level 60).

  Fixpoint value_of (fuel : nat) (env : environment) (exp : expression) (cont : continuation) : option behavior :=
    match fuel with
    | O => None
    | S fuel' =>
      match exp with
      | ExpConst n => apply_cont fuel' cont (ValNum (Z.of_nat n))
      | ExpDiff exp1 exp2 => value_of fuel' env exp1 (ContDiff1 exp2 env cont)
      | ExpIsZero exp1 => value_of fuel' env exp1 (ContIsZero cont)
      | ExpIf exp1 exp2 exp3 => value_of fuel' env exp1 (ContIf exp2 exp3 env cont)
      | ExpVar x =>
        match apply_env env x with
        | BehVal val => apply_cont fuel' cont val
        | BehErr => Some BehErr
        end
      | ExpLet x exp1 exp2 => value_of fuel' env exp1 (ContLet x exp2 env cont)
      | ExpProc x exp1 => apply_cont fuel' cont (ValClo x exp1 env)
      | ExpCall exp1 exp2 => value_of fuel' env exp1 (ContCall1 exp2 env cont)
      | ExpLetrec p_name b_var p_body exp1 =>
        value_of fuel' (extend_env_rec env p_name b_var p_body) exp1 cont
      end
    end

  with apply_cont (fuel : nat) (cont : continuation) (beh : behavior) : option behavior :=
         match fuel with
         | O => None
         | S fuel' =>
           match cont with
           | ContEnd => Some beh
           | ContDiff1 exp2 env cont' =>
             val1 <- beh;
               value_of fuel' env exp2 (ContDiff2 val1 cont')
           | ContDiff2 val1 cont' =>
             val2 <- beh;
               match (val1, val2) with
               | (ValNum n1, ValNum n2) => apply_cont fuel' cont' (ValNum (n1 - n2))
               | _ => Some BehErr
               end
           | ContIsZero cont' =>
             val1 <- beh;
               match val1 with
               | ValNum n1 => apply_cont fuel' cont' (ValBool (Z.eqb n1 0))
               | _ => Some BehErr
               end
           | ContIf exp2 exp3 env cont' =>
             val1 <- beh;
               match val1 with
               | ValBool true => value_of fuel' env exp2 cont'
               | ValBool false => value_of fuel' env exp3 cont'
               | _ => Some BehErr
               end
           | ContLet x exp2 env cont' =>
             val1 <- beh;
               value_of fuel' (extend_env env x val1) exp2 cont'
           | ContCall1 exp2 env cont' =>
             val1 <- beh;
               value_of fuel' env exp2 (ContCall2 val1 cont')
           | ContCall2 val1 cont' =>
             val2 <- beh;
               match val1 with
               | ValClo x exp saved_env => value_of fuel' (extend_env saved_env x val2) exp cont'
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
                  end.
  
  Ltac invert' H := inversion H; clear H; subst.

  Inductive value_of_rel__cont : environment -> term -> continuation -> behavior -> Prop :=
  | VrelCont :
      forall env tm beh cont beh',
        value_of_rel env tm beh ->
        apply_cont_rel cont beh beh' ->
        value_of_rel__cont env tm cont beh'

  with apply_cont_rel : continuation -> behavior -> behavior -> Prop :=
       | ArelEnd :
           forall beh,
             apply_cont_rel ContEnd beh beh
       | ArelDiff1_abort :
           forall beh1 exp2 env cont',
             abort beh1 ->
             apply_cont_rel (ContDiff1 exp2 env cont') beh1 beh1
       | ArelDiff1 :
           forall env exp2 val1 cont' beh,
             value_of_rel__cont env exp2 (ContDiff2 val1 cont') beh -> 
             apply_cont_rel (ContDiff1 exp2 env cont') val1 beh
       | ArelDiff2_abort :
           forall beh2 val1 cont',
             abort beh2 ->
             apply_cont_rel (ContDiff2 val1 cont') beh2 beh2
       | ArelDiff2 :
           forall cont' n1 n2 beh,
             apply_cont_rel cont' (ValNum (n1 - n2)) beh ->
             apply_cont_rel (ContDiff2 (ValNum n1) cont') (ValNum n2) beh
       | ArelDiff2_err :
           forall val1 val2 cont',
             ~(is_num val1 /\ is_num val2) ->
             apply_cont_rel (ContDiff2 val1 cont') val2 BehErr
       | ArelIsZero_abort :
           forall beh1 cont',
             abort beh1 ->
             apply_cont_rel (ContIsZero cont') beh1 beh1
       | ArelIsZero :
           forall cont' n1 beh,
             apply_cont_rel cont' (ValBool (Z.eqb n1 0)) beh ->
             apply_cont_rel (ContIsZero cont') (ValNum n1) beh
       | ArelIsZero_err :
           forall val1 cont',
             ~is_num val1 ->
             apply_cont_rel (ContIsZero cont') val1 BehErr
       | ArelIf_abort :
           forall beh1 exp2 exp3 env cont',
             abort beh1 ->
             apply_cont_rel (ContIf exp2 exp3 env cont') beh1 beh1
       | ArelIfTrue :
           forall env exp2 cont' beh exp3,
             value_of_rel__cont env exp2 cont' beh ->
             apply_cont_rel (ContIf exp2 exp3 env cont') (ValBool true) beh
       | ArelIfFalse :
           forall env exp3 cont' beh exp2,
             value_of_rel__cont env exp3 cont' beh ->
             apply_cont_rel (ContIf exp2 exp3 env cont') (ValBool false) beh
       | ArelIf_err :
           forall val1 exp2 exp3 env cont',
             ~is_bool val1 ->
             apply_cont_rel (ContIf exp2 exp3 env cont') val1 BehErr
       | ArelLet_abort :
           forall beh1 x exp2 env cont',
             abort beh1 ->
             apply_cont_rel (ContLet x exp2 env cont') beh1 beh1
       | ArelLet :
           forall env x val1 exp2 cont' beh,
             value_of_rel__cont (extend_env env x val1) exp2 cont' beh ->
             apply_cont_rel (ContLet x exp2 env cont') val1 beh
       | ArelCall1_abort :
           forall beh1 exp2 env cont',
             abort beh1 ->
             apply_cont_rel (ContCall1 exp2 env cont') beh1 beh1
       | ArelCall1 :
           forall env exp2 val1 cont' beh,
             value_of_rel__cont env exp2 (ContCall2 val1 cont') beh ->
             apply_cont_rel (ContCall1 exp2 env cont') val1 beh
       | ArelCall2_abort :
           forall beh2 val1 cont',
             abort beh2 ->
             apply_cont_rel (ContCall2 val1 cont') beh2 beh2
       | ArelCall2 :
           forall saved_env x val2 exp cont' beh,
             value_of_rel__cont (extend_env saved_env x val2) exp cont' beh ->
             apply_cont_rel (ContCall2 (ValClo x exp saved_env) cont') val2 beh
       | ArelCall2_err :
           forall val1 cont' val2,
             ~is_clo val1 ->
             apply_cont_rel (ContCall2 val1 cont') val2 BehErr.

  Hint Constructors value_of_rel__cont apply_cont_rel.

  Scheme Induction for value_of_rel__cont Sort Prop
  with Induction for apply_cont_rel Sort Prop.

  Hint Extern 1 => match goal with
                  | [ H : Some _ = Some _ |- _ ] => invert' H
                  | [ H : abort _ |- _ ] => invert' H
                  end.

  Lemma apply_cont_rel_err :
    forall cont, apply_cont_rel cont BehErr BehErr.
  Proof.
    destruct cont; eauto.
  Qed.

  Hint Resolve apply_cont_rel_err.
  
  Theorem value_of_soundness__cont :
    forall fuel env exp beh cont,
      value_of fuel env exp cont = Some beh ->
      value_of_rel__cont env exp cont beh
      with apply_cont_soundness :
             forall fuel cont beh beh',
               apply_cont fuel cont beh = Some beh' ->
               apply_cont_rel cont beh beh'.
  Proof.
    induction fuel; intros; try discriminate.
    clear value_of_soundness__cont.
    destruct exp; eauto.
    {
      simpl in H.
      apply IHfuel in H.
      invert' H.
      destruct beh0.
      {
        invert' H1; eauto.
        invert' H6.
        destruct beh0; eauto.
        {
          invert' H1; eauto.
        }
        {
          invert' H1; eauto.
        }
      }
      {
        invert' H1; eauto.
      }
    }
    {
      simpl in H.
      apply IHfuel in H.
      invert' H.
      destruct beh0; eauto.
      {
        invert' H1; eauto.
      }
      {
        invert' H1; eauto.
      }
    }
    {
      simpl in H.
      apply IHfuel in H.
      invert' H.
      destruct beh0.
      {
        invert' H1; eauto.
        {
          invert' H7; eauto.
        }
        {
          invert' H7; eauto.
        }
      }
      {
        invert' H1; eauto.
      }
    }
    {
      simpl in H.
      destruct (apply_env env v) eqn:?.
      {
        apply apply_cont_soundness in H.
        apply VrelCont with (beh := BehVal e); eauto.
        rewrite <- Heqb.
        eauto.
      }
      {
        invert' H.
        apply VrelCont with (beh := BehErr); eauto.
        rewrite <- Heqb.
        eauto.
      }
    }
    {
      simpl in H.
      apply IHfuel in H.
      invert' H.
      destruct beh0.
      {
        invert' H1; eauto.
        invert' H7; eauto.
      }
      {
        invert' H1; eauto.
      }
    }
    {
      simpl in H.
      apply IHfuel in H.
      invert' H.
      destruct beh0.
      {
        invert' H1; eauto.
        invert' H6.
        invert' H1; eauto.
        {
          invert' H6; eauto.
        }
        {
          invert' H6; eauto.
        }
      }
      {
        invert' H1; eauto.
      }
    }
    {
      simpl in H.
      invert' H.
      apply IHfuel in H1.
      invert' H1.
      eauto.
    }

    induction fuel; intros; try discriminate.
    clear apply_cont_soundness.
    destruct cont.
    {
      simpl in H.
      eauto.
    }
    {
      simpl in H.
      destruct beh; eauto.
    }
    {
      simpl in H.
      destruct beh; eauto.
      destruct e; eauto.
      destruct e0; eauto.
    }
    {
      simpl in H.
      destruct beh; eauto.
      destruct e; eauto.
    }
    {
      simpl in H.
      destruct beh; eauto.
      destruct e2; eauto.
      destruct b; eauto.
    }
    {
      simpl in H.
      destruct beh; eauto.
    }
    {
      simpl in H.
      destruct beh; eauto.
    }
    {
      simpl in H.
      destruct beh; eauto.
      destruct e; eauto.
    }
  Qed.

  Theorem value_of_soundness :
    forall env exp beh,
      (exists fuel, value_of fuel env exp ContEnd = Some beh) ->
      value_of_rel env exp beh.
  Proof.
    intros.
    destruct H.
    apply value_of_soundness__cont in H.
    invert' H.
    invert' H1.
    assumption.
  Qed.

  Definition value_of_term (fuel : nat) (env : environment) (tm : term) (cont : continuation) : option behavior :=
    match tm with
    | TmExp exp => value_of fuel env exp cont
    | TmDiff1 beh1 exp2 =>
      val1 <- beh1;
        value_of fuel env exp2 (ContDiff2 val1 cont)
    | TmDiff2 val1 beh2 =>
      val2 <- beh2;
        match (val1, val2) with
        | (ValNum n1, ValNum n2) => apply_cont fuel cont (BehVal (ValNum (n1 - n2)))
        | _ => Some BehErr
        end
    | TmIsZero1 beh1 =>
      val1 <- beh1;
        match val1 with
        | ValNum n1 => apply_cont fuel cont (BehVal (ValBool (Z.eqb n1 0)))
        | _ => Some BehErr
        end
    | TmIf1 beh1 exp2 exp3 =>
      val1 <- beh1;
        match val1 with
        | ValBool true => value_of fuel env exp2 cont
        | ValBool false => value_of fuel env exp3 cont
        | _ => Some BehErr
        end
    | TmLet1 x beh1 exp2 =>
      val1 <- beh1;
        value_of fuel (extend_env env x val1) exp2 cont
    | TmCall1 beh1 exp2 =>
      val1 <- beh1;
        value_of fuel env exp2 (ContCall2 val1 cont)
    | TmCall2 val1 beh2 =>
      val2 <- beh2;
        match val1 with
        | ValClo x exp saved_env =>
          value_of fuel (extend_env saved_env x val2) exp cont
        | _ => Some BehErr
        end
    end.

  Lemma value_of_fuel_incr :
    forall fuel env exp cont beh,
      value_of fuel env exp cont = Some beh ->
      value_of (S fuel) env exp cont = Some beh
  with apply_cont_fuel_incr :
         forall fuel cont beh beh',
           apply_cont fuel cont beh = Some beh' ->
           apply_cont (S fuel) cont beh = Some beh'.
  Proof.
    induction fuel; intros; simpl in H; subst; try discriminate.
    clear value_of_fuel_incr.
    destruct exp;
      repeat match goal with
             | [ _ : context[match value_of ?FUEL ?ENV ?EXP ?CONT with Some _ => _ | None => _ end] |- _ ] =>
               destruct (value_of FUEL ENV EXP CONT) eqn:?; try congruence
             | [ _ : context[match ?BEH with BehVal _ => _ | BehErr => _ end] |- _ ] =>
               destruct BEH eqn:?; try congruence
             | [ _ : context[match ?VAL with ValNum _ => _ | ValBool _ => _ | ValClo _ _ _ => _ end] |- _ ] =>
               destruct VAL; try congruence
             | [ _ : context[if ?B then _ else _] |- _ ] =>
               destruct B
             end;
      eauto.
    {
      simpl.
      rewrite Heqb.
      apply apply_cont_fuel_incr in H.
      eauto.
    }
    {
      simpl.
      rewrite Heqb.
      eauto.
    }

    induction fuel; intros; simpl in H; subst; try discriminate.
    clear apply_cont_fuel_incr.
    destruct cont;
      repeat match goal with
             | [ _ : context[match apply_cont ?FUEL ?CONT ?BEH with Some _ => _ | None => _ end] |- _ ] =>
               destruct (apply_cont FUEL CONT BEH) eqn:?; try congruence
             | [ _ : context[match ?BEH with BehVal _ => _ | BehErr => _ end] |- _ ] =>
               destruct BEH; try congruence
             | [ _ : context[match ?VAL with ValNum _ => _ | ValBool _ => _ | ValClo _ _ _ => _ end] |- _ ] =>
               destruct VAL; try congruence
             | [ _ : context[if ?B then _ else _] |- _ ] =>
               destruct B
             end;
      eauto.
  Qed.

  Hint Resolve value_of_fuel_incr apply_cont_fuel_incr.

  Lemma value_of_fuel_order :
    forall fuel env exp cont beh fuel',
      value_of fuel env exp cont = Some beh ->
      fuel <= fuel' ->
      value_of fuel' env exp cont = Some beh.
  Proof.
    induction 2; auto.
  Qed.

  Lemma apply_cont_fuel_order :
    forall fuel cont beh beh' fuel',
      apply_cont fuel cont beh = Some beh' ->
      fuel <= fuel' ->
      apply_cont fuel' cont beh = Some beh'.
  Proof.
    induction 2; eauto.
  Qed.
    
  Hint Resolve value_of_fuel_order apply_cont_fuel_order.

  Lemma fuel_order_tm :
    forall fuel env tm cont beh fuel',
      value_of_term fuel env tm cont = Some beh ->
      fuel <= fuel' ->
      value_of_term fuel' env tm cont = Some beh.
  Proof.
    intros; destruct tm; simpl in *; eauto;
    repeat match goal with
           | [ _ : context[match value_of ?FUEL ?ENV ?EXP ?CONT with Some _ => _ | None => _ end] |- _ ] =>
             destruct (value_of FUEL ENV EXP CONT) eqn:T; try congruence; apply value_of_fuel_order with (fuel' := fuel') in T; eauto; rewrite T
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

  Lemma apply_cont_err :
    forall fuel cont beh,
      apply_cont fuel cont BehErr = Some beh ->
      beh = BehErr.
  Proof.
    intros.
    destruct fuel; try discriminate.
    simpl in H.
    destruct cont; eauto.
  Qed.

  Theorem value_of_term_completeness__cont :
    forall env tm cont beh,
      value_of_rel__cont env tm cont beh ->
      exists fuel, value_of_term fuel env tm cont = Some beh.
  Proof.
    apply (value_of_rel__cont_ind_dep
             (fun env tm cont beh (H : value_of_rel__cont env tm cont beh) => exists fuel, value_of_term fuel env tm cont = Some beh)
             (fun cont beh beh' (H : apply_cont_rel cont beh beh') => exists fuel, apply_cont fuel cont beh = Some beh')); intros.
    generalize dependent cont.
    generalize dependent beh'.
    induction v; intros; eauto; simpl.
    {
      destruct H.
      exists (S x).
      eauto.
    }
    {
      apply IHv2 in a; eauto.
      destruct a.
      simpl in H0.
      destruct beh1.
      {
        assert (apply_cont_rel (ContDiff1 exp2 env cont) e beh'); eauto.
        constructor.
        apply value_of_soundness__cont with (fuel := x); eauto.
        apply IHv1 in H1; eauto.
        destruct H1.
        simpl in H1.
        exists (S x0).
        eauto.
        exists (S x).
        eauto.
      }
      {
        invert' H0.
        assert (apply_cont_rel (ContDiff1 exp2 env cont) BehErr BehErr); eauto.
        apply IHv1 in H0; eauto.
        destruct H0.
        exists (S x0).
        eauto.
        exists 1.
        eauto.
      }
    }
    {
      invert' H.
      destruct H0.
      apply apply_cont_err in H.
      subst.
      eauto.
    }
    {
      apply IHv2 in a; eauto.
      destruct a.
      simpl in H0.
      destruct beh2.
      {
        destruct val1.
        {
          destruct e.
          {
            assert (apply_cont_rel (ContDiff2 (ValNum z) cont) (ValNum z0) beh'); eauto.
            constructor.
            apply apply_cont_soundness with (fuel := x); eauto.
            apply IHv1 in H1; eauto.
            exists (S x).
            eauto.
          }
          {
            invert' H0.
            assert (apply_cont_rel (ContDiff2 (ValNum z) cont) (ValBool b) BehErr); eauto.
            apply IHv1 in H0; eauto.
            exists 1.
            eauto.
          }
          {
            invert' H0.
            assert (apply_cont_rel (ContDiff2 (ValNum z) cont) (ValClo v e e0) BehErr); eauto.
            apply IHv1 in H0; eauto.
            exists 1.
            eauto.
          }
        }
        {
          invert' H0.
          assert (apply_cont_rel (ContDiff2 (ValBool b) cont) e BehErr); eauto.
          apply IHv1 in H0; eauto.
          exists 1.
          eauto.
        }
        {
          invert' H0.
          assert (apply_cont_rel (ContDiff2 (ValClo v e0 e1) cont) e BehErr); eauto.
          apply IHv1 in H0; eauto.
          exists 1.
          eauto.
        }
      }
      {
        invert' H0.
        assert (apply_cont_rel (ContDiff2 val1 cont) BehErr BehErr); eauto.
        apply IHv1 in H0; eauto.
        exists 1.
        eauto.
      }
    }
    {
      destruct beh2; eauto.
      destruct H0.
      apply apply_cont_err in H0.
      subst.
      eauto.
    }
    {
      destruct H0.
      apply apply_cont_err in H0.
      subst.
      destruct val1, val2; exists 1; eauto.
      contradict H.
      eauto.
    }
    {
      apply IHv2 in a; eauto.
      destruct a.
      simpl in H0.
      destruct beh1.
      {
        destruct e.
        {
          assert (apply_cont_rel (ContIsZero cont) (ValNum z) beh'); eauto.
          constructor.
          apply apply_cont_soundness with (fuel := x); eauto.
          apply IHv1 in H1; eauto.
          destruct H1.
          simpl in H1.
          exists (S x0).
          eauto.
          exists (S x).
          eauto.
        }
        {
          invert' H0.
          assert (apply_cont_rel (ContIsZero cont) (ValBool b) BehErr); eauto.
          apply IHv1 in H0; eauto.
          destruct H0.
          exists (S x0).
          eauto.
          exists 1.
          eauto.
        }
        {
          invert' H0.
          assert (apply_cont_rel (ContIsZero cont) (ValClo v e e0) BehErr); eauto.
          apply IHv1 in H0; eauto.
          destruct H0.
          exists (S x0).
          eauto.
          exists 1.
          eauto.
        }
      }
      {
        invert' H0.
        assert (apply_cont_rel (ContIsZero cont) BehErr BehErr); eauto.
        apply IHv1 in H0; eauto.
        destruct H0.
        exists (S x0).
        eauto.
        exists 1.
        eauto.
      }
    }
    {
      invert' H.
      destruct H0.
      apply apply_cont_err in H.
      subst.
      eauto.
    }
    {
      destruct val1.
      {
        contradict H.
        eauto.
      }
      {
        destruct H0.
        apply apply_cont_err in H0.
        subst.
        eauto.
      }
      {
        destruct H0.
        apply apply_cont_err in H0.
        subst.
        eauto.
      }
    }
    {
      apply IHv2 in a; eauto.
      destruct a.
      simpl in H0.
      destruct beh1.
      {
        destruct e.
        {
          invert' H.
          assert (apply_cont_rel (ContIf exp2 exp3 env cont) (ValNum z) BehErr); eauto.
          apply IHv1 in H; eauto.
          destruct H.
          simpl in H.
          exists (S x1).
          eauto.
          exists 1.
          eauto.
        }
        {
          destruct b.
          {
            assert (apply_cont_rel (ContIf exp2 exp3 env cont) (ValBool true) beh'); eauto.
            constructor.
            apply value_of_soundness__cont with (fuel := x); eauto.
            apply IHv1 in H1; eauto.
            destruct H1.
            simpl in H1.
            exists (S x0).
            eauto.
            exists (S x).
            eauto.
          }
          {
            assert (apply_cont_rel (ContIf exp2 exp3 env cont) (ValBool false) beh'); eauto.
            constructor.
            apply value_of_soundness__cont with (fuel := x); eauto.
            apply IHv1 in H1; eauto.
            destruct H1.
            exists (S x0).
            eauto.
            exists (S x).
            eauto.
          }
        }
        {
          invert' H0.
          assert (apply_cont_rel (ContIf exp2 exp3 env cont) (ValClo v e e0) BehErr); eauto.
          apply IHv1 in H0; eauto.
          destruct H0.
          simpl in H0.
          exists (S x0).
          eauto.
          exists 1.
          eauto.
        }
      }
      {
        invert' H0.
        assert (apply_cont_rel (ContIf exp2 exp3 env cont) BehErr BehErr); eauto.
        apply IHv1 in H0; eauto.
        destruct H0.
        simpl in H0.
        exists (S x0).
        eauto.
        exists 1.
        eauto.
      }
    }
    {
      invert' H.
      destruct H0.
      apply apply_cont_err in H.
      subst.
      eauto.
    }
    {
      destruct H0.
      apply apply_cont_err in H0.
      subst.
      destruct val1; eauto.
      contradict H.
      eauto.
    }
    {
      destruct H.
      exists (S x0).
      simpl.
      destruct (apply_env env x) eqn:?; eauto.
      apply apply_cont_err in H.
      subst.
      eauto.
    }
    {
      apply IHv2 in a; eauto.
      destruct a.
      simpl in H0.
      destruct beh1.
      {
        assert (apply_cont_rel (ContLet x exp2 env cont) e beh'); eauto.
        constructor.
        apply value_of_soundness__cont with (fuel := x0); eauto.
        apply IHv1 in H1; eauto.
        destruct H1.
        simpl in H1.
        exists (S x1).
        eauto.
        exists (S x0).
        eauto.
      }
      {
        invert' H0.
        assert (apply_cont_rel (ContLet x exp2 env cont) BehErr BehErr); eauto.
        apply IHv1 in H0; eauto.
        destruct H0.
        simpl in H0.
        exists (S x1).
        eauto.
        exists 1.
        eauto.
      }
    }
    {
      invert' H.
      destruct H0.
      apply apply_cont_err in H.
      subst.
      eauto.
    }
    {      
      destruct H.
      exists (S x0).
      eauto.
    }
    {
      apply IHv2 in a; eauto.
      destruct a.
      simpl in H0.
      destruct beh1.
      {
        assert (apply_cont_rel (ContCall1 exp2 env cont) e beh'); eauto.
        constructor.
        apply value_of_soundness__cont with (fuel := x); eauto.
        apply IHv1 in H1; eauto.
        destruct H1.
        simpl in H1.
        exists (S x0).
        eauto.
        exists (S x).
        eauto.
      }
      {
        invert' H0.
        assert (apply_cont_rel (ContCall1 exp2 env cont) BehErr BehErr); eauto.
        apply IHv1 in H0.
        destruct H0.
        simpl in H0.
        exists (S x0).
        eauto.
        exists 1.
        eauto.
      }
    }      
    {
      invert' H.
      destruct H0.
      apply apply_cont_err in H.
      subst.
      eauto.
    }
    {
      apply IHv2 in a; eauto.
      destruct a.
      simpl in H0.
      destruct beh2.
      {
        destruct val1.
        {
          invert' H0.
          assert (apply_cont_rel (ContCall2 (ValNum z) cont) e BehErr); eauto.
          apply IHv1 in H0; eauto.
          exists 1.
          eauto.
        }
        {
          invert' H0.
          assert (apply_cont_rel (ContCall2 (ValBool b) cont) e BehErr); eauto.
          apply IHv1 in H0; eauto.
          exists 1.
          eauto.
        }
        {
          assert (apply_cont_rel (ContCall2 (ValClo v e0 e1) cont) e beh'); eauto.
          constructor.
          apply value_of_soundness__cont with (fuel := x); eauto.
          apply IHv1 in H1; eauto.
          exists (S x).
          eauto.
        }
      }
      {
        invert' H0.
        assert (apply_cont_rel (ContCall2 val1 cont) BehErr BehErr); eauto.
        apply IHv1 in H0; eauto.
        exists 1.
        eauto.
      }
    }
    {
      invert' H.
      destruct H0.
      apply apply_cont_err in H.
      subst.
      eauto.
    }
    {
      destruct H0.
      apply apply_cont_err in H0.
      subst.
      destruct val1; eauto.
      contradict H.
      eauto.
    }
    {
      apply IHv in a; eauto.
      destruct a.
      simpl in H0.
      exists (S x).
      eauto.
    }

    {
      exists 1.
      eauto.
    }
    {
      invert' a.
      exists 1.
      eauto.
    }
    {
      destruct H.
      exists (S x).
      eauto.
    }
    {
      invert' a.
      exists 1.
      eauto.
    }
    {
      destruct H.
      exists (S x).
      eauto.
    }
    {
      destruct val1, val2; exists 1; eauto.
      contradict n.
      eauto.
    }
    {
      invert' a.
      exists 1.
      eauto.
    }
    {
      destruct H.
      exists (S x).
      eauto.
    }
    {
      destruct val1; exists 1; eauto.
      contradict n.
      eauto.
    }
    {
      invert' a.
      exists 1.
      eauto.
    }
    {
      destruct H.
      exists (S x).
      eauto.
    }
    {
      destruct H.
      exists (S x).
      eauto.
    }
    {
      destruct val1; exists 1; eauto.
      contradict n.
      eauto.
    }
    {
      invert' a.
      exists 1.
      eauto.
    }
    {
      destruct H.
      exists (S x0).
      eauto.
    }
    {
      invert' a.
      exists 1.
      eauto.
    }
    {
      destruct H.
      exists (S x).
      eauto.
    }
    {
      invert' a.
      exists 1.
      eauto.
    }
    {
      destruct H.
      exists (S x0).
      eauto.
    }
    {
      destruct val1; exists 1; eauto.
      contradict n.
      eauto.
    }
  Qed.

  Theorem value_of_term_completeness :
    forall env tm beh,
      value_of_rel env tm beh ->
      exists fuel, value_of_term fuel env tm ContEnd = Some beh.
  Proof.
    intros.
    assert (T := VrelCont H (ArelEnd beh)).
    apply value_of_term_completeness__cont in T.
    assumption.
  Qed.

  Theorem value_of_completeness :
    forall env exp beh,
      value_of_rel env exp beh ->
      exists fuel, value_of fuel env exp ContEnd = Some beh.
  Proof.
    intros.
    apply value_of_term_completeness in H; auto.
  Qed.

  Hint Resolve value_of_soundness value_of_completeness.

  Theorem value_of_correctness :
    forall env exp beh,
      (exists fuel, value_of fuel env exp ContEnd = Some beh) <->
      value_of_rel env exp beh.
  Proof.
    intuition.
  Qed.
End LetrecImpl.

Export LetrecImpl.