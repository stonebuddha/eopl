Require Import Bool ZArith Arith String List Max Logic.Eqdep_dec.
Set Implicit Arguments.

Notation "x <- e1 ; e2" :=
    (match e1 with
    | None => None
    | Some x => e2
    end)
(right associativity, at level 60).

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
    | Clo : string -> expression -> environment -> expval

    with environment : Set :=
    | Empty : environment
    | Extend : string -> expval -> environment -> environment
    .

    Scheme expval_mut := Induction for expval Sort Prop
    with environment_mut := Induction for environment Sort Prop.

    Fixpoint assoc_error (x : string) (env : environment) : option expval :=
        match env with
        | Empty => None
        | Extend y val saved_env => if string_dec x y then Some val else assoc_error x saved_env
        end.

    Inductive value_of_rel : expression -> environment -> expval -> Prop :=
    | VConst : forall num env, value_of_rel (Const num) env (Num (Z.of_nat num))
    | VDiff : forall exp1 exp2 num1 num2 env, value_of_rel exp1 env (Num num1) -> value_of_rel exp2 env (Num num2) -> value_of_rel (Diff exp1 exp2) env (Num (num1 - num2))
    | VIsZero : forall exp1 num1 env, value_of_rel exp1 env (Num num1) -> value_of_rel (IsZero exp1) env (Bool (Z.eqb num1 0))
    | VIfTrue : forall exp1 exp2 exp3 val2 env, value_of_rel exp1 env (Bool true) -> value_of_rel exp2 env val2 -> value_of_rel (If exp1 exp2 exp3) env val2
    | VIfFalse : forall exp1 exp2 exp3 val3 env, value_of_rel exp1 env (Bool false) -> value_of_rel exp3 env val3 -> value_of_rel (If exp1 exp2 exp3) env val3
    | VVar : forall var env val, assoc_error var env = Some val -> value_of_rel (Var var) env val
    | VLet : forall var exp1 body env val1 valb, value_of_rel exp1 env val1 -> value_of_rel body (Extend var val1 env) valb -> value_of_rel (Let var exp1 body) env valb
    | VProc : forall var body env, value_of_rel (Proc var body) env (Clo var body env)
    | VCall : forall rator rand env var body saved_env rand_val valb, value_of_rel rator env (Clo var body saved_env) -> value_of_rel rand env rand_val -> value_of_rel body (Extend var rand_val saved_env) valb -> value_of_rel (Call rator rand) env valb
    .
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
    | Call : forall ctx, expression ctx -> expression ctx -> expression ctx
    .

    Inductive expval : Set :=
    | Num : Z -> expval
    | Bool : bool -> expval
    | Clo : forall ctx, expression (S ctx) -> environment ctx -> expval

    with environment : nat -> Set :=
    | Empty : environment O
    | Extend : forall ctx, expval -> environment ctx -> environment (S ctx)
    .

    Scheme expval_mut := Induction for expval Sort Prop
    with environment_mut := Induction for environment Sort Prop.

    Lemma nltz : forall n, n < O -> False.
        intro; omega.
    Qed.

    Fixpoint nth {ctx : nat} (n : nat) (env : environment ctx) : n < ctx -> expval :=
        match env in (environment ctx) with
        | Empty => fun pf => match nltz pf with end
        | Extend _ val saved_env =>
                match n with
                | O => fun _ => val
                | S _ => fun pf => nth saved_env (lt_S_n _ _ pf)
                end
        end.

    Inductive value_of_rel: forall ctx, expression ctx -> environment ctx -> expval -> Prop :=
    | VConst : forall ctx num env, value_of_rel (Const ctx num) env (Num (Z.of_nat num))
    | VDiff : forall ctx (exp1 : expression ctx) exp2 num1 num2 env, value_of_rel exp1 env (Num num1) -> value_of_rel exp2 env (Num num2) -> value_of_rel (Diff exp1 exp2) env (Num (num1 - num2))
    | VIsZero : forall ctx (exp1 : expression ctx) num1 env, value_of_rel exp1 env (Num num1) -> value_of_rel (IsZero exp1) env (Bool (Z.eqb num1 0))
    | VIfTrue : forall ctx (exp1 : expression ctx) exp2 exp3 val2 env, value_of_rel exp1 env (Bool true) -> value_of_rel exp2 env val2 -> value_of_rel (If exp1 exp2 exp3) env val2
    | VIfFalse : forall ctx (exp1 : expression ctx) exp2 exp3 val3 env, value_of_rel exp1 env (Bool false) -> value_of_rel exp3 env val3 -> value_of_rel (If exp1 exp2 exp3) env val3
    | VVar : forall ctx n (pf : n < ctx) env val, nth env pf = val -> value_of_rel (Var pf) env val
    | VLet : forall ctx (exp1 : expression ctx) body env val1 val, value_of_rel exp1 env val1 -> value_of_rel body (Extend val1 env) val -> value_of_rel (Let exp1 body) env val
    | VProc : forall ctx (body : expression (S ctx)) env, value_of_rel (Proc body) env (Clo body env)
    | VCall : forall ctx (rator : expression ctx) rand env ctx' (body : expression (S ctx')) saved_env rand_val val, value_of_rel rator env (Clo body saved_env) -> value_of_rel rand env rand_val -> value_of_rel body (Extend rand_val saved_env) val -> value_of_rel (Call rator rand) env val
    .

    Lemma value_of_rel_diff_inversion : forall ctx (exp1 : expression ctx) exp2 env val, value_of_rel (Diff exp1 exp2) env val -> exists num1 num2, value_of_rel exp1 env (Num num1) /\ value_of_rel exp2 env (Num num2) /\ val = Num (num1 - num2).
        Hint Resolve eq_nat_dec.
        intros.
        inversion H.
        apply inj_pair2_eq_dec in H0; auto.
        apply inj_pair2_eq_dec in H1; auto.
        apply inj_pair2_eq_dec in H3; auto.
        subst.
        eauto.
    Qed.

    Lemma value_of_rel_is_zero_inversion : forall ctx (exp1 : expression ctx) env val, value_of_rel (IsZero exp1) env val -> exists num1, value_of_rel exp1 env (Num num1) /\ val = Bool (Z.eqb num1 0).
        Hint Resolve eq_nat_dec.
        intros.
        inversion H.
        apply inj_pair2_eq_dec in H0; auto.
        apply inj_pair2_eq_dec in H2; auto.
        subst.
        eauto.
    Qed.

    Lemma value_of_rel_if_inversion : forall ctx (exp1 : expression ctx) exp2 exp3 env val, value_of_rel (If exp1 exp2 exp3) env val -> (value_of_rel exp1 env (Bool true) /\ value_of_rel exp2 env val) \/ (value_of_rel exp1 env (Bool false) /\ value_of_rel exp3 env val).
        Hint Resolve eq_nat_dec.
        intros.
        inversion H.
            left.
            apply inj_pair2_eq_dec in H0; auto.
            apply inj_pair2_eq_dec in H1; auto.
            apply inj_pair2_eq_dec in H5; auto.
            subst.
            auto.

            right.
            apply inj_pair2_eq_dec in H0; auto.
            apply inj_pair2_eq_dec in H4; auto.
            apply inj_pair2_eq_dec in H5; auto.
            subst.
            auto.
    Qed.

    Lemma value_of_rel_let_inversion : forall ctx (exp1 : expression ctx) body env val, value_of_rel (Let exp1 body) env val -> exists val1, value_of_rel exp1 env val1 /\ value_of_rel body (Extend val1 env) val.
        Hint Resolve eq_nat_dec.
        intros.
        inversion H.
        apply inj_pair2_eq_dec in H0; auto.
        apply inj_pair2_eq_dec in H1; auto.
        apply inj_pair2_eq_dec in H3; auto.
        subst.
        eauto.
    Qed.

    Lemma value_of_rel_var_inversion : forall ctx n (pf : n < ctx) env val, value_of_rel (Var pf) env val -> exists (pf : n < ctx), nth env pf = val.
        Hint Resolve eq_nat_dec.
        intros.
        inversion H.
        apply inj_pair2_eq_dec in H2; auto.
        subst.
        eauto.
    Qed.

    Lemma value_of_rel_proc_inversion : forall ctx (body : expression (S ctx)) env val, value_of_rel (Proc body) env val -> val = Clo body env.
        Hint Resolve eq_nat_dec.
        intros.
        inversion H.
        apply inj_pair2_eq_dec in H2; auto.
        apply inj_pair2_eq_dec in H3; auto.
        subst.
        auto.
    Qed.

    Lemma value_of_rel_call_inversion : forall ctx (rator : expression ctx) rand env val, value_of_rel (Call rator rand) env val -> exists ctx' (body : expression (S ctx')) saved_env rand_val, value_of_rel rator env (Clo body saved_env) /\ value_of_rel rand env rand_val /\ value_of_rel body (Extend rand_val saved_env ) val.
        Hint Resolve eq_nat_dec.
        intros.
        inversion H.
        apply inj_pair2_eq_dec in H0; auto.
        apply inj_pair2_eq_dec in H1; auto.
        apply inj_pair2_eq_dec in H2; auto.
        subst.
        exists ctx'.
        exists body.
        eauto.
    Qed.

    Inductive exp_equiv : forall ctx ctx', expression ctx -> expression ctx' -> Prop :=
    | EQConst : forall ctx ctx' num num', ctx = ctx' -> num = num' -> exp_equiv (Const ctx num) (Const ctx' num')
    | EQDiff : forall ctx ctx' (exp1 : expression ctx) (exp1' : expression ctx') exp2 exp2', exp_equiv exp1 exp1' -> exp_equiv exp2 exp2' -> exp_equiv (Diff exp1 exp2) (Diff exp1' exp2')
    | EQIsZero : forall ctx ctx' (exp1 : expression ctx) (exp1' : expression ctx'), exp_equiv exp1 exp1' -> exp_equiv (IsZero exp1) (IsZero exp1')
    | EQIf : forall ctx ctx' (exp1 : expression ctx) (exp1' : expression ctx') exp2 exp2' exp3 exp3', exp_equiv exp1 exp1' -> exp_equiv exp2 exp2' -> exp_equiv exp3 exp3' -> exp_equiv (If exp1 exp2 exp3) (If exp1' exp2' exp3')
    | EQLet : forall ctx ctx' (exp1 : expression ctx) (exp1' : expression ctx') body body', exp_equiv exp1 exp1' -> exp_equiv body body' -> exp_equiv (Let exp1 body) (Let exp1' body')
    | EQVar : forall ctx ctx' n n' (pf : n < ctx) (pf' : n' < ctx'), ctx = ctx' -> n = n' -> exp_equiv (Var pf) (Var pf')
    | EQProc : forall ctx ctx' (body : expression (S ctx)) (body' : expression (S ctx')), exp_equiv body body' -> exp_equiv (Proc body) (Proc body')
    | EQCall : forall ctx ctx' (rator : expression ctx) (rator' : expression ctx') rand rand', exp_equiv rator rator' -> exp_equiv rand rand' -> exp_equiv (Call rator rand) (Call rator' rand')
    .

    Inductive expval_equiv : expval -> expval -> Prop :=
    | EQNum : forall num num', num = num' -> expval_equiv (Num num) (Num num')
    | EQBool : forall bool bool', bool = bool' -> expval_equiv (Bool bool) (Bool bool')
    | EQClo : forall ctx ctx' (body : expression (S ctx)) (body' : expression (S ctx')) saved_env saved_env', exp_equiv body body' -> env_equiv saved_env saved_env' -> expval_equiv (Clo body saved_env) (Clo body' saved_env')

    with env_equiv : forall ctx ctx', environment ctx -> environment ctx' -> Prop :=
    | EQEmpty : env_equiv Empty Empty
    | EQExtend : forall ctx ctx' (saved_env : environment ctx) (saved_env' : environment ctx') val val', expval_equiv val val' -> env_equiv saved_env saved_env' -> env_equiv (Extend val saved_env) (Extend val' saved_env')
    .

    Hint Constructors exp_equiv expval_equiv env_equiv.

    Lemma exp_equiv_refl : forall ctx (exp : expression ctx), exp_equiv exp exp.
        induction exp; eauto.
    Qed.

    Lemma exp_equiv_comm : forall ctx ctx' (exp : expression ctx) (exp' : expression ctx'), exp_equiv exp exp' -> exp_equiv exp' exp.
        intros.
        induction H; auto.
    Qed.

    Lemma exp_equiv_tran : forall ctx ctx' ctx'' (exp : expression ctx) (exp' : expression ctx') (exp'' : expression ctx''), exp_equiv exp exp' -> exp_equiv exp' exp'' -> exp_equiv exp exp''.
    Admitted.

    Lemma exp_equiv_const_inversion : forall ctx (exp : expression ctx) ctx' num', exp_equiv exp (Const ctx' num') -> exists num, ctx = ctx' /\ num = num' /\ exp = Const ctx num.
        Hint Resolve eq_nat_dec.
        intros.
        inversion H.
        apply inj_pair2_eq_dec in H0; auto.
        eauto.
    Qed.

    Lemma exp_equiv_diff_inversion : forall ctx ctx' (exp : expression ctx) (exp1' : expression ctx') exp2', exp_equiv exp (Diff exp1' exp2') -> exists exp1 exp2, exp_equiv exp1 exp1' /\ exp_equiv exp2 exp2' /\ exp = Diff exp1 exp2.
        Hint Resolve eq_nat_dec.
        intros.
        inversion H.
        apply inj_pair2_eq_dec in H0; auto.
        apply inj_pair2_eq_dec in H1; auto.
        apply inj_pair2_eq_dec in H4; auto.
        subst.
        eauto.
    Qed.

    Lemma exp_equiv_var_inversion : forall ctx (exp : expression ctx) ctx' n' (pf' : n' < ctx'), exp_equiv exp (Var pf') -> exists n (pf : n < ctx), ctx = ctx' /\ n = n' /\ exp = Var pf.
        Hint Resolve eq_nat_dec.
        intros.
        inversion H.
        apply inj_pair2_eq_dec in H0; auto.
        subst.
        eauto.
    Qed.

    Lemma expval_equiv_refl : forall val, expval_equiv val val
    with env_equiv_refl : forall env, expval_equiv env env.
    Admitted.

    Fixpoint value_of {ctx : nat} (fuel : nat) (exp : expression ctx) : environment ctx -> option expval :=
        match fuel with
        | O => fun _ => None
        | S fuel' =>
                match exp with
                | Const _ num => fun _ => Some (Num (Z.of_nat num))
                | Diff _ exp1 exp2 => fun env =>
                        val1 <- value_of fuel' exp1 env;
                        val2 <- value_of fuel' exp2 env;
                        match (val1, val2) with
                        | (Num num1, Num num2) => Some (Num (num1 - num2))
                        | _ => None
                        end
                | IsZero _ exp1 => fun env =>
                        val1 <- value_of fuel' exp1 env;
                        match val1 with
                        | Num num1 => Some (Bool (Z.eqb num1 0))
                        | _ => None
                        end
                | If _ exp1 exp2 exp3 => fun env =>
                        val1 <- value_of fuel' exp1 env;
                        match val1 with
                        | Bool true => value_of fuel' exp2 env
                        | Bool false => value_of fuel' exp3 env
                        | _ => None
                        end
                | Var _ _ pf => fun env => Some (nth env pf)
                | Let _ exp1 body => fun env =>
                        val1 <- value_of fuel' exp1 env;
                        value_of fuel' body (Extend val1 env)
                | Proc _ body => fun env => Some (Clo body env)
                | Call _ rator rand => fun env =>
                        rator_val <- value_of fuel' rator env;
                        match rator_val with
                        | Clo _ body saved_env =>
                                rand_val <- value_of fuel' rand env;
                                value_of fuel' body (Extend rand_val saved_env)
                        | _ => None
                        end
                end
        end.

    Lemma value_of_diff_equation : forall fuel ctx (exp1 : expression ctx) exp2 env num1 num2, value_of fuel exp1 env = Some (Num num1) -> value_of fuel exp2 env = Some (Num num2) -> value_of (S fuel) (Diff exp1 exp2) env = Some (Num (num1 - num2)).
        intros.
        simpl.
        rewrite -> H.
        rewrite -> H0.
        trivial.
    Qed.

    Lemma value_of_is_zero_equation : forall fuel ctx (exp1 : expression ctx) env num1, value_of fuel exp1 env = Some (Num num1) -> value_of (S fuel) (IsZero exp1) env = Some (Bool (Z.eqb num1 0)).
        intros.
        simpl.
        rewrite -> H.
        trivial.
    Qed.

    Lemma value_of_if_true_equation : forall fuel ctx (exp1 : expression ctx) exp2 exp3 env val, value_of fuel exp1 env = Some (Bool true) -> value_of fuel exp2 env = Some val -> value_of (S fuel) (If exp1 exp2 exp3) env = Some val.
        intros.
        simpl.
        rewrite -> H.
        trivial.
    Qed.

    Lemma value_of_if_false_equation : forall fuel ctx (exp1 : expression ctx) exp2 exp3 env val, value_of fuel exp1 env = Some (Bool false) -> value_of fuel exp3 env = Some val -> value_of (S fuel) (If exp1 exp2 exp3) env = Some val.
        intros.
        simpl.
        rewrite -> H.
        trivial.
    Qed.

    Lemma value_of_var_equation : forall fuel ctx (env : environment ctx) n (pf : n < ctx) val, nth env pf = val -> value_of (S fuel) (Var pf) env = Some val.
        intros.
        simpl.
        rewrite -> H.
        trivial.
    Qed.

    Lemma value_of_let_equation : forall fuel ctx (exp1 : expression ctx) body env val1 val, value_of fuel exp1 env = Some val1 -> value_of fuel body (Extend val1 env) = Some val -> value_of (S fuel) (Let exp1 body) env = Some val.
        intros.
        simpl.
        rewrite -> H.
        trivial.
    Qed.

    Lemma value_of_call_equation : forall fuel ctx (rator : expression ctx) rand env rand_val val ctx' (body : expression (S ctx')) saved_env, value_of fuel rator env = Some (Clo body saved_env) -> value_of fuel rand env = Some rand_val -> value_of fuel body (Extend rand_val saved_env) = Some val -> value_of (S fuel) (Call rator rand) env = Some val.
        intros.
        simpl.
        rewrite -> H.
        rewrite -> H0.
        trivial.
    Qed.

    Hint Resolve value_of_diff_equation value_of_is_zero_equation value_of_if_true_equation value_of_if_false_equation value_of_var_equation value_of_let_equation value_of_call_equation.
    Hint Constructors value_of_rel.

    Theorem value_of_soundness : forall ctx (exp : expression ctx) env val, (exists fuel, value_of fuel exp env = Some val) -> value_of_rel exp env val.
        intros.
        destruct 0 as [ fuel ? ].
        generalize dependent ctx.
        generalize dependent val.
        induction fuel; intros; try discriminate; destruct exp;
        match goal with
        | [ H : value_of _ _ _ = _ |- _ ] => simpl in H
        end;
        repeat (try match goal with
                    | [ _ : context[match value_of ?FUEL ?EXP ?ENV with Some _ => _ | None => _ end] |- _ ] => destruct (value_of FUEL EXP ENV) eqn:?; try discriminate
                    | [ _ : context[match ?VAL with Num _ => _ | Bool _ => _ | Clo _ _ _ => _ end] |- _ ] => destruct VAL; try discriminate
                    | [ _ : context[if ?B then _ else _] |- _ ] => destruct B
                    | [ H : Some _ = Some _ |- _ ] => inversion H; subst
                    end;
                eauto).
    Qed.

    Lemma fuel_incr : forall fuel ctx (exp : expression ctx) env val, value_of fuel exp env = Some val -> value_of (S fuel) exp env = Some val.
        induction fuel; intros; try discriminate; destruct exp;
        match goal with
        | [ H : value_of _ _ _ = _ |- _ ] => simpl in H
        end;
        repeat (try match goal with
                    | [ _ : context[match value_of ?FUEL ?EXP ?ENV with Some _ => _ | None => _ end] |- _ ] => destruct (value_of FUEL EXP ENV) eqn:?; try discriminate
                    | [ _ : context[match ?VAL with Num _ => _ | Bool _ => _ | Clo _ _ _ => _ end] |- _ ] => destruct VAL; try discriminate
                    | [ _ : context[if ?B then _ else _] |- _ ] => destruct B
                    | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
                    end;
                eauto).
    Qed.

    Lemma fuel_order : forall ctx (exp : expression ctx) env val fuel fuel', value_of fuel exp env = Some val -> fuel <= fuel' -> value_of fuel' exp env = Some val.
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

    Theorem value_of_completeness : forall ctx (exp : expression ctx) env val, value_of_rel exp env val -> exists fuel, value_of fuel exp env = Some val.
        Hint Resolve fuel_order le_max_l le_max_r le_max_1 le_max_2 le_max_3.
        induction 1;
        match goal with
        | [ IH1 : exists _, _, IH2 : exists _, _, IH3 : exists _, _ |- _ ] => destruct IH1 as [ fuel1 ? ]; destruct IH2 as [ fuel2 ? ]; destruct IH3 as [ fuel3 ? ]; exists (S (max (max fuel1 fuel2) fuel3))
        | [ IH1 : exists _, _, IH2 : exists _, _ |- _ ] => destruct IH1 as [ fuel1 ? ]; destruct IH2 as [ fuel2 ? ]; exists (S (max fuel1 fuel2))
        | [ IH1 : exists _, _ |- _ ] => destruct IH1 as [ fuel1 ? ]; exists (S fuel1)
        | [ |- _ ] => exists (S O)
        end;
        eauto.
    Qed.

    Theorem value_of_correctness : forall ctx (exp : expression ctx) env val, (exists fuel, value_of fuel exp env = Some val) <-> value_of_rel exp env val.
        Hint Resolve value_of_soundness value_of_completeness.
        intros; split; auto.
    Qed.
End Lexical.

Module Translation.
    Definition static_environment := list string.
    Definition empty_senv : static_environment := nil.
    Definition extend_senv (x : string) (senv : static_environment) : static_environment := x :: senv.

    Lemma find_index_lemma1 : forall y (saved_senv : static_environment), O < length (y :: saved_senv).
        intros.
        simpl.
        omega.
    Qed.

    Lemma find_index_lemma2 : forall n y (saved_senv : static_environment), n < length saved_senv -> (S n) < length (y :: saved_senv).
        intros.
        simpl.
        omega.
    Qed.

    Fixpoint find_index (x : string) (senv : static_environment) : option { n : nat | n < length senv } :=
        match senv with
        | nil => None
        | y :: saved_senv =>
                if string_dec x y then
                    Some (exist _ O (find_index_lemma1 _ _))
                else
                    res <- find_index x saved_senv;
                    match res with
                    | exist n pf => Some (exist _ (S n) (find_index_lemma2 _ _ pf))
                    end
        end.

    Fixpoint translation_of (exp : Proc.expression) (senv : static_environment) : option (Lexical.expression (length senv)) :=
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
                | exist _ pf => Some (Lexical.Var pf)
                end
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

    Lemma tranlation_of_const_equation : forall exp senv num, translation_of exp senv = Some (Lexical.Const (length senv) num) -> exp = Proc.Const num.
        intros.
        destruct exp; simpl in H;
        repeat (try match goal with
                    | [ _ : context[match translation_of ?EXP ?SENV with Some _ => _ | None => _ end] |- _ ] => destruct (translation_of EXP SENV); try discriminate
                    | [ _ : context[match find_index ?VAR ?SENV with Some _ => _ | None => _ end] |- _ ] => destruct (find_index VAR SENV); try discriminate
                    | [ H : Some _ = Some _ |- _ ] => inversion H
                    end;
                auto).
        destruct s0.
        inversion H.
    Qed.

    Lemma translation_of_diff_equation : forall exp senv exp1' exp2', translation_of exp senv = Some (Lexical.Diff exp1' exp2') -> exists exp1 exp2, translation_of exp1 senv = Some exp1' /\ translation_of exp2 senv = Some exp2' /\ exp = Proc.Diff exp1 exp2.
        intros.
        Hint Resolve eq_nat_dec.
        destruct exp; simpl in H;
        repeat (try match goal with
                    | [ _ : context[match translation_of ?EXP ?SENV with Some _ => _ | None => _ end] |- _ ] => destruct (translation_of EXP SENV) eqn:?; try discriminate
                    | [ _ : context[match find_index ?VAR ?SENV with Some _ => _ | None => _ end] |- _ ] => destruct (find_index VAR SENV) eqn:?; try discriminate
                    | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
                    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2_eq_dec in H; auto; subst
                    end;
                eauto).
        destruct s0.
        inversion H.
    Qed.

    Lemma translation_of_var_equation : forall exp senv n (pf : n < length senv), translation_of exp senv = Some (Lexical.Var pf) -> exists var pf', find_index var senv = Some (exist _ n pf')  /\ exp = Proc.Var var.
        intros.
        Hint Resolve eq_nat_dec.
        destruct exp; simpl in H;
        repeat (try match goal with
                    | [ _ : context[match translation_of ?EXP ?SENV with Some _ => _ | None => _ end] |- _ ] => destruct (translation_of EXP SENV) eqn:?; try discriminate
                    | [ _ : context[match find_index ?VAR ?SENV with Some _ => _ | None => _ end] |- _ ] => destruct (find_index VAR SENV) eqn:?; try discriminate
                    | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
                    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2_eq_dec in H; auto; subst
                    end;
                eauto).
        destruct s0.
        inversion H.
        subst.
        eauto.
    Qed.

    Fixpoint proc_environment_to_static_environment (env : Proc.environment) : static_environment :=
        match env with
        | Proc.Empty => nil
        | Proc.Extend x _ saved_env => x :: proc_environment_to_static_environment saved_env
        end.

    Fixpoint length_proc_environment (env : Proc.environment) : nat :=
        match env with
        | Proc.Empty => O
        | Proc.Extend _ _ saved_env => S (length_proc_environment saved_env)
        end.

    Fixpoint translation_of_expval (val : Proc.expval) : option Lexical.expval :=
        match val with
        | Proc.Num num => Some (Lexical.Num num)
        | Proc.Bool bool => Some (Lexical.Bool bool)
        | Proc.Clo var body saved_env =>
                body <- translation_of body (extend_senv var (proc_environment_to_static_environment saved_env));
                saved_env <- translation_of_environment saved_env;
                Some (Lexical.Clo body saved_env)
        end

    with translation_of_environment (env : Proc.environment) : option (Lexical.environment (length (proc_environment_to_static_environment env))) :=
        match env with
        | Proc.Empty => Some Lexical.Empty
        | Proc.Extend _ val saved_env =>
                val <- translation_of_expval val;
                saved_env <- translation_of_environment saved_env;
                Some (Lexical.Extend val saved_env)
        end.

    Hint Constructors Proc.value_of_rel Lexical.value_of_rel.
    Hint Constructors Lexical.exp_equiv Lexical.expval_equiv Lexical.env_equiv.
    Hint Resolve Lexical.exp_equiv_refl Lexical.expval_equiv_refl Lexical.env_equiv_refl.

    Lemma translation_of_expval_inversion_num : forall val num, translation_of_expval val = Some (Lexical.Num num) -> val = Proc.Num num.
        intros.
        destruct val.
            simpl in H.
            inversion H.
            trivial.

            simpl in H.
            inversion H.

            simpl in H.
            repeat (
                match goal with
                | [ _ : context[translation_of ?EXP ?SENV] |- _ ] => destruct (translation_of EXP SENV); try discriminate
                | [ _ : context[translation_of_environment ?ENV] |- _ ] => destruct (translation_of_environment ENV); try discriminate
                end).
    Qed.

    Lemma translation_of_expval_inversion_bool : forall val bool, translation_of_expval val = Some (Lexical.Bool bool) -> val = Proc.Bool bool.
        intros.
        destruct val.
            simpl in H.
            inversion H.

            simpl in H.
            inversion H.
            trivial.

            simpl in H.
            repeat (
                match goal with
                | [ _ : context[translation_of ?EXP ?SENV] |- _ ] => destruct (translation_of EXP SENV); try discriminate
                | [ _ : context[translation_of_environment ?ENV] |- _ ] => destruct (translation_of_environment ENV); try discriminate
                end).
    Qed.

    Lemma translation_of_expval_inversion_clo : forall val ctx (body' : Lexical.expression (S ctx)) saved_env', translation_of_expval val = Some (Lexical.Clo body' saved_env') -> exists var body saved_env bodyt saved_envt, val = Proc.Clo var body saved_env /\ translation_of_environment saved_env = Some saved_envt /\ Lexical.env_equiv saved_envt saved_env' /\ translation_of body (extend_senv var (proc_environment_to_static_environment saved_env)) = Some bodyt /\ Lexical.exp_equiv bodyt body'.
        intros.
    Admitted.

    Lemma var_in_environment : forall env s env' x (pf : x < length (proc_environment_to_static_environment env)) (pf' : x < length (proc_environment_to_static_environment env)) val', Lexical.nth env' pf = val' -> find_index s (proc_environment_to_static_environment env) = Some (exist _ x pf') -> translation_of_environment env = Some env' -> exists val valt, translation_of_expval val = Some valt /\ Lexical.expval_equiv valt val' /\ Proc.assoc_error s env = Some val.
        intros.
    Admitted.

    Lemma translation_of_soundness_generalized : forall exp env ctx' env' (exp' : Lexical.expression ctx') val' expt envt, translation_of exp (proc_environment_to_static_environment env) = Some expt -> Lexical.exp_equiv expt exp' -> translation_of_environment env = Some envt -> Lexical.env_equiv envt env' -> Lexical.value_of_rel exp' env' val' -> exists val valt, translation_of_expval val = Some valt /\ Lexical.expval_equiv valt val' /\ Proc.value_of_rel exp env val.
        intros.
        generalize dependent exp.
        generalize dependent env.
        induction H3; intros.

        apply Lexical.exp_equiv_const_inversion in H0.
        destruct H0.
        destruct H0.
        destruct H3.
        subst.
        apply tranlation_of_const_equation in H.
        subst.
        exists (Proc.Num (Z.of_nat num)).
        exists (Lexical.Num (Z.of_nat num)).
        auto.

        apply Lexical.exp_equiv_diff_inversion in H0.
        destruct H0.
        destruct H0.
        destruct H0.
        destruct H3.
        subst.
        apply translation_of_diff_equation in H.
        destruct H.
        destruct H.
        destruct H.
        destruct H4.
        subst.
        assert (T1 := IHvalue_of_rel1 env0 x envt).
        eapply T1 in H0; eauto.
        destruct H0.
        destruct H0.
        destruct H0.
        destruct H5.
        subst.
        inversion H5.
        subst.
        apply translation_of_expval_inversion_num in H0.
        subst.
        assert (T2 := IHvalue_of_rel2 env0 x0 envt).
        eapply T2 in H3; eauto.
        destruct H3.
        destruct H0.
        destruct H0.
        destruct H3.
        subst.
        inversion H3.
        subst.
        apply translation_of_expval_inversion_num in H0.
        subst.
        exists (Proc.Num (num1 - num2)).
        exists (Lexical.Num (num1 - num2)).
        auto.

        admit.

        admit.

        admit.

        apply Lexical.exp_equiv_var_inversion in H0.
        destruct H0.
        destruct H0.
        destruct H0.
        destruct H4.
        subst.
        apply translation_of_var_equation in H3.
        destruct H3.
        destruct H.
        destruct H.
        subst.
        assert (Lexical.nth envt pf = Lexical.nth envt pf).
        trivial.
        apply var_in_environment with (s := x) (pf' := x1) in H0; auto.
        admit.

        admit.

        admit.
    Admitted.

    Theorem translation_of_soundness : forall exp exp' val', translation_of exp empty_senv = Some exp' -> Lexical.value_of_rel exp' Lexical.Empty val' -> exists val valt, translation_of_expval val = Some valt /\ Lexical.expval_equiv valt val' /\ Proc.value_of_rel exp Proc.Empty val.
        intros; eapply translation_of_soundness_generalized; eauto; auto.
    Qed.

    Lemma translation_of_completeness_generalized : forall env env' exp exp' val val', translation_of exp (proc_environment_to_static_environment env) = Some exp' -> translation_of_environment env = Some env' -> translation_of_expval val = Some val' -> Proc.value_of_rel exp env val -> Lexical.value_of_rel exp' env' val'.
    Admitted.

    Theorem translation_of_completeness : forall exp exp' val val', translation_of exp (proc_environment_to_static_environment Proc.Empty) = Some exp' -> translation_of_expval val = Some val' -> Proc.value_of_rel exp Proc.Empty val -> Lexical.value_of_rel exp' Lexical.Empty val'.
        intros; eapply translation_of_completeness_generalized; eauto; auto.
    Qed.
End Translation.
