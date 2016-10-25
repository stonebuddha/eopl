Require Import Bool ZArith Arith String List Max Logic.Eqdep_dec Program.Equality.
Open Scope string_scope.
Set Implicit Arguments.

Notation "x <- e1 ; e2" :=
    (match e1 with
    | None => None
    | Some x => e2
    end)
(right associativity, at level 60).

Ltac simplify := repeat
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

    Inductive exp_equiv : forall ctx, expression ctx -> expression ctx -> Prop :=
    | EQConst : forall ctx num, exp_equiv (Const ctx num) (Const ctx num)
    | EQDiff : forall ctx (exp1 : expression ctx) exp2 exp1' exp2', exp_equiv exp1 exp1' -> exp_equiv exp2 exp2' -> exp_equiv (Diff exp1 exp2) (Diff exp1' exp2')
    | EIsZero : forall ctx (exp1 : expression ctx) exp1', exp_equiv exp1 exp1' -> exp_equiv (IsZero exp1) (IsZero exp1')
    | EIf : forall ctx (exp1 : expression ctx) exp2 exp3 exp1' exp2' exp3', exp_equiv exp1 exp1' -> exp_equiv exp2 exp2' -> exp_equiv exp3 exp3' -> exp_equiv (If exp1 exp2 exp3) (If exp1' exp2' exp3')
    | EVar : forall ctx n (pf : n < ctx) (pf' : n < ctx), exp_equiv (Var pf) (Var pf')
    | ELet : forall ctx (exp1 : expression ctx) body exp1' body', exp_equiv exp1 exp1' -> exp_equiv body body' -> exp_equiv (Let exp1 body) (Let exp1' body')
    | EProc : forall ctx (body : expression (S ctx)) body', exp_equiv body body' -> exp_equiv (Proc body) (Proc body')
    | ECall : forall ctx (rator : expression ctx) rand rator' rand', exp_equiv rator rator' -> exp_equiv rand rand' -> exp_equiv (Call rator rand) (Call rator' rand')
    .

    Hint Constructors expression exp_equiv.
    Hint Resolve eq_nat_dec inj_pair2_eq_dec.

    Lemma exp_equiv_refl : forall ctx (exp : expression ctx), exp_equiv exp exp.
        induction exp; eauto.
    Qed.

    Hint Resolve exp_equiv_refl.

    Ltac existT_inversion :=
        repeat (match goal with
                | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2_eq_dec in H; auto
                end); subst; eauto 10.

    Lemma exp_equiv_const_inversion_left : forall ctx num exp2, exp_equiv (Const ctx num) exp2 -> exp2 = Const ctx num.
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma exp_equiv_diff_inversion_left : forall ctx (exp11 : expression ctx) exp12 exp2, exp_equiv (Diff exp11 exp12) exp2 -> exists exp21 exp22, exp2 = Diff exp21 exp22 /\ exp_equiv exp11 exp21 /\ exp_equiv exp12 exp22.
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma exp_equiv_is_zero_inversion_left : forall ctx (exp11 : expression ctx) exp2, exp_equiv (IsZero exp11) exp2 -> exists exp21, exp2 = IsZero exp21 /\ exp_equiv exp11 exp21.
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma exp_equiv_if_inversion_left : forall ctx (exp11 : expression ctx) exp12 exp13 exp2, exp_equiv (If exp11 exp12 exp13) exp2 -> exists exp21 exp22 exp23, exp2 = If exp21 exp22 exp23 /\ exp_equiv exp11 exp21 /\ exp_equiv exp12 exp22 /\ exp_equiv exp13 exp23.
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma exp_equiv_var_inversion_left : forall ctx n (pf1 : n < ctx) exp2, exp_equiv (Var pf1) exp2 -> exists (pf2 : n < ctx), exp2 = Var pf2.
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma exp_equiv_let_inversion_left : forall ctx (exp11 : expression ctx) body1 exp2, exp_equiv (Let exp11 body1) exp2 -> exists exp21 body2, exp2 = Let exp21 body2 /\ exp_equiv exp11 exp21 /\ exp_equiv body1 body2.
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma exp_equiv_proc_inversion_left : forall ctx (body1 : expression (S ctx)) exp2, exp_equiv (Proc body1) exp2 -> exists body2, exp2 = Proc body2 /\ exp_equiv body1 body2.
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma exp_equiv_call_inversion_left : forall ctx (rator1 : expression ctx) rand1 exp2, exp_equiv (Call rator1 rand1) exp2 -> exists rator2 rand2, exp2 = Call rator2 rand2 /\ exp_equiv rator1 rator2 /\ exp_equiv rand1 rand2.
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Ltac exp_equiv_inversion H :=
        match type of H with
        | exp_equiv (Const _ _) _ => apply exp_equiv_const_inversion_left in H
        | exp_equiv (Diff _ _) _ => apply exp_equiv_diff_inversion_left in H
        | exp_equiv (IsZero _) _ => apply exp_equiv_is_zero_inversion_left in H
        | exp_equiv (If _ _ _) _ => apply exp_equiv_if_inversion_left in H
        | exp_equiv (Var _) _ => apply exp_equiv_var_inversion_left in H
        | exp_equiv (Let _ _) _ => apply exp_equiv_let_inversion_left in H
        | exp_equiv (Proc _) _ => apply exp_equiv_proc_inversion_left in H
        | exp_equiv (Call _ _) _ => apply exp_equiv_call_inversion_left in H
        end; simplify.

    Lemma exp_equiv_symm : forall ctx (exp1 : expression ctx) exp2, exp_equiv exp1 exp2 -> exp_equiv exp2 exp1.
        induction exp1; intros;
        repeat (try match goal with
                    | [ H : exp_equiv _ _ |- _ ] => exp_equiv_inversion H
                    | [ IH : forall _, _ |- _ ] => eapply IH
                    end;
                eauto).
    Qed.

    Lemma exp_equiv_trans : forall ctx (exp1 : expression ctx) exp2 exp3, exp_equiv exp1 exp2 -> exp_equiv exp2 exp3 -> exp_equiv exp1 exp3.
        induction exp1; intros;
        repeat (try match goal with
                    | [ H : exp_equiv _ _ |- _ ] => exp_equiv_inversion H
                    end;
                eauto).
    Qed.

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

    Lemma value_of_rel_const_inversion : forall ctx num env val, value_of_rel (Const ctx num) env val -> val = Num (Z.of_nat num).
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma value_of_rel_diff_inversion : forall ctx (exp1 : expression ctx) exp2 env val, value_of_rel (Diff exp1 exp2) env val -> exists num1 num2, value_of_rel exp1 env (Num num1) /\ value_of_rel exp2 env (Num num2) /\ val = Num (num1 - num2).
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma value_of_rel_is_zero_inversion : forall ctx (exp1 : expression ctx) env val, value_of_rel (IsZero exp1) env val -> exists num1, value_of_rel exp1 env (Num num1) /\ val = Bool (Z.eqb num1 0).
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma value_of_rel_if_inversion : forall ctx (exp1 : expression ctx) exp2 exp3 env val, value_of_rel (If exp1 exp2 exp3) env val -> (value_of_rel exp1 env (Bool true) /\ value_of_rel exp2 env val) \/ (value_of_rel exp1 env (Bool false) /\ value_of_rel exp3 env val).
        intros.
        inversion H;
        existT_inversion.
    Qed.

    Lemma value_of_rel_let_inversion : forall ctx (exp1 : expression ctx) body env val, value_of_rel (Let exp1 body) env val -> exists val1, value_of_rel exp1 env val1 /\ value_of_rel body (Extend val1 env) val.
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma value_of_rel_var_inversion : forall ctx n (pf : n < ctx) env val, value_of_rel (Var pf) env val -> exists (pf : n < ctx), nth env pf = val.
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma value_of_rel_proc_inversion : forall ctx (body : expression (S ctx)) env val, value_of_rel (Proc body) env val -> val = Clo body env.
        intros.
        inversion H.
        existT_inversion.
    Qed.

    Lemma value_of_rel_call_inversion : forall ctx (rator : expression ctx) rand env val, value_of_rel (Call rator rand) env val -> exists ctx' (body : expression (S ctx')) saved_env rand_val, value_of_rel rator env (Clo body saved_env) /\ value_of_rel rand env rand_val /\ value_of_rel body (Extend rand_val saved_env ) val.
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
    Inductive static_environment : nat -> Set :=
    | Empty : static_environment O
    | Extend : forall ctx, string -> static_environment ctx -> static_environment (S ctx)
    .

    Fixpoint find_index {ctx : nat} (x : string) (senv : static_environment ctx) : option { n : nat | n < ctx } :=
        match senv with
        | Empty => None
        | Extend _ y saved_senv =>
                if string_dec x y then
                    Some (exist _ O (lt_0_Sn _))
                else
                    res <- find_index x saved_senv;
                    match res with
                    | exist n pf => Some (exist _ (S n) (lt_n_S _ _ pf))
                    end
        end.

    Fixpoint nth {ctx : nat} (n : nat) (senv : static_environment ctx) : n < ctx -> string :=
        match senv in (static_environment ctx) with
        | Empty => fun pf => match Lexical.nltz pf with end
        | Extend _ x saved_senv =>
                match n with
                | O => fun _ => x
                | S n' => fun pf => nth saved_senv (lt_S_n _ _ pf)
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
                | exist _ pf => Some (Lexical.Var pf)
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
        repeat (try match goal with
                    | [ _ : context[match translation_of ?EXP ?SENV with Some _ => _ | None => _ end] |- _ ] => destruct (translation_of EXP SENV) eqn:?; try discriminate
                    | [ _ : context[match find_index ?S ?SENV with Some _ => _ | None => _ end] |- _ ] => destruct (find_index S SENV) eqn:?; try discriminate
                    | [ _ : context[let (_, _) := ?BIND in _] |- _ ] => destruct BIND
                    | [ H : Some _ = Some _ |- _ ] => inversion H; subst; clear H
                    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2_eq_dec in H; try apply eq_nat_dec; subst
                    end;
                eauto 10).

    Lemma translation_of_const_inversion : forall ctx exp (senv : static_environment ctx) num, translation_of exp senv = Some (Lexical.Const _ num) -> exp = Proc.Const num.
        intros.
        rewrite translation_of_equation in H.
        destruct exp;
        translation_of_inversion_finisher.
    Qed.

    Lemma translation_of_diff_inversion : forall ctx exp (senv : static_environment ctx) exp1' exp2', translation_of exp senv = Some (Lexical.Diff exp1' exp2') -> exists exp1 exp2, exp = Proc.Diff exp1 exp2 /\ translation_of exp1 senv = Some exp1' /\ translation_of exp2 senv = Some exp2'.
        intros.
        rewrite translation_of_equation in H.
        destruct exp;
        translation_of_inversion_finisher.
    Qed.

    Lemma translation_of_var_inversion : forall ctx exp (senv : static_environment ctx) n (pf : n < ctx), translation_of exp senv = Some (Lexical.Var pf) -> exists var (pf' : n < ctx), exp = Proc.Var var /\ find_index var senv = Some (exist _ n pf').
        intros.
        rewrite translation_of_equation in H.
        destruct exp;
        translation_of_inversion_finisher.
    Qed.

    Fixpoint length_proc_environment (env : Proc.environment) : nat :=
        match env with
        | Proc.Empty => O
        | Proc.Extend _ _ saved_env => S (length_proc_environment saved_env)
        end.

    Inductive proc_env_static_env_rel : forall ctx, Proc.environment -> static_environment ctx -> Prop :=
    | PSEmpty : proc_env_static_env_rel (Proc.Empty) Empty
    | PSExtend : forall ctx x val saved_env (saved_senv : static_environment ctx), proc_env_static_env_rel saved_env saved_senv -> proc_env_static_env_rel (Proc.Extend x val saved_env) (Extend x saved_senv)
    .

    Inductive proc_env_lexical_env_rel : forall ctx, Proc.environment -> Lexical.environment ctx -> Prop :=
    | PLEmpty : proc_env_lexical_env_rel (Proc.Empty) (Lexical.Empty)
    | PLExtend : forall ctx saved_env (saved_env' : Lexical.environment ctx) val val' x, proc_env_lexical_env_rel saved_env saved_env' -> proc_val_lexical_val_rel val val' -> proc_env_lexical_env_rel (Proc.Extend x val saved_env) (Lexical.Extend val' saved_env')

    with proc_val_lexical_val_rel : Proc.expval -> Lexical.expval -> Prop :=
    | PLNum : forall num, proc_val_lexical_val_rel (Proc.Num num) (Lexical.Num num)
    | PLBool : forall bool, proc_val_lexical_val_rel (Proc.Bool bool) (Lexical.Bool bool)
    | PLClo : forall ctx saved_env (saved_env' : Lexical.environment ctx) senv body bodyt body' x, proc_env_static_env_rel saved_env senv -> translation_of body (Extend x senv) = Some bodyt -> Lexical.exp_equiv bodyt body' -> proc_env_lexical_env_rel saved_env saved_env' -> proc_val_lexical_val_rel (Proc.Clo x body saved_env) (Lexical.Clo body' saved_env')
    .

    Hint Constructors proc_env_static_env_rel proc_env_lexical_env_rel proc_val_lexical_val_rel.
    Hint Constructors Proc.expression Proc.expval Proc.environment Proc.value_of_rel.
    Hint Constructors Lexical.expression Lexical.expval Lexical.environment Lexical.value_of_rel.
    Hint Constructors static_environment.
    Hint Constructors Lexical.exp_equiv.
    Hint Resolve Lexical.exp_equiv_refl Lexical.exp_equiv_symm Lexical.exp_equiv_trans.

    Fixpoint generate_string (len : nat) : string :=
        match len with
        | O => ""
        | S len' => "+" ++ (generate_string len')
        end.

    Fixpoint generate (ctx : nat) : static_environment ctx :=
        match ctx with
        | O => Empty
        | S ctx' => Extend (generate_string ctx) (generate ctx')
        end.

    Lemma nth_different_proof : forall ctx (senv : static_environment ctx) n (pf : n < ctx) (pf' : n < ctx), nth senv pf = nth senv pf'.
        intros.
        dependent induction senv.
            inversion pf.
            destruct n; eauto.
    Qed.

    Lemma find_index_none : forall var ctx (senv : static_environment ctx) n (pf : n < ctx), find_index var senv = None -> nth senv pf <> var.
        intros.
        contradict H.
        dependent induction senv.
            inversion pf.
            destruct n.
                simpl in H.
                simpl.
                destruct (string_dec var s); congruence.

                simpl in H.
                apply IHsenv in H.
                simpl.
                destruct (string_dec var s); try congruence.
                destruct (find_index var senv); try congruence.
                destruct s0.
                congruence.
    Qed.

    Lemma nth_generate : forall ctx senv n (pf : n < ctx), senv = generate ctx -> nth senv pf = generate_string (ctx - n).
        intros.
        generalize dependent n.
        dependent induction senv; intros.
            inversion pf.
            destruct n.
                simpl.
                simpl in H.
                inversion H.
                auto.

                simpl in H.
                inversion H.
                apply inj_pair2_eq_dec in H2; try apply eq_nat_dec.
                apply IHsenv with (n := n) (pf := lt_S_n _ _ pf) in H2.
                simpl.
                auto.
    Qed.

    Lemma length_generate : forall n, String.length (generate_string n) = n.
        intros.
        induction n.
            auto.
            simpl.
            omega.
    Qed.

    Lemma length_equal : forall s1 s2, s1 = s2 -> String.length s1 = String.length s2.
        intros.
        induction s1; induction s2; congruence.
    Qed.

    Lemma find_index_some : forall ctx n (pf : n < ctx) senv, senv = generate ctx -> exists pf', find_index (nth senv pf) senv = Some (exist _ n pf').
        intros.
        generalize dependent n.
        dependent induction senv; intros.
            inversion pf.
            destruct n.
                simpl.
                destruct (string_dec s s).
                    eauto.
                    congruence.
            simpl in H.
            inversion H.
            apply inj_pair2_eq_dec in H2; try apply eq_nat_dec.
            assert (H3 := H2).
            apply IHsenv with (n := n) (pf := lt_S_n _ _ pf) in H2.
            destruct H2.
            exists (lt_n_S _ _ x).
            simpl.
            destruct (string_dec (nth senv (lt_S_n n ctx pf))).
                assert (T := nth_generate (lt_S_n n ctx pf) H3).
                rewrite -> T in e.
                apply length_equal in e.
                simpl in e.
                assert (String.length (generate_string (ctx - n)) = ctx - n). apply length_generate.
                assert (String.length (generate_string ctx) = ctx). apply length_generate.
                rewrite -> H2 in e.
                rewrite -> H4 in e.
                contradict e.
                omega.

                rewrite -> H0.
                auto.
    Qed.

    Lemma proc_exp_construction : forall ctx (exp' : Lexical.expression ctx) (senv : static_environment ctx), senv = generate ctx -> exists exp expt, translation_of exp senv = Some expt /\ Lexical.exp_equiv expt exp'.
        intros.
        dependent induction exp'.
            exists (Proc.Const n).
            exists (Lexical.Const _ n).
            auto.

            assert (T1 := IHexp'1 senv).
            assert (Q1 := H).
            apply T1 in Q1.
            destruct Q1.
            destruct H0.
            destruct H0.
            assert (T2 := IHexp'2 senv).
            assert (Q2 := H).
            apply T2 in Q2.
            destruct Q2.
            destruct H2.
            destruct H2.
            exists (Proc.Diff x x1).
            exists (Lexical.Diff x0 x2).
            simpl.
            rewrite -> H0.
            rewrite -> H2.
            auto.

            assert (T1 := IHexp' senv).
            assert (Q1 := H).
            apply T1 in Q1.
            destruct Q1.
            destruct H0.
            destruct H0.
            exists (Proc.IsZero x).
            exists (Lexical.IsZero x0).
            simpl.
            rewrite -> H0.
            auto.

            assert (T1 := IHexp'1 senv).
            assert (Q1 := H).
            apply T1 in Q1.
            destruct Q1.
            destruct H0.
            destruct H0.
            assert (T2 := IHexp'2 senv).
            assert (Q2 := H).
            apply T2 in Q2.
            destruct Q2.
            destruct H2.
            destruct H2.
            assert (T3 := IHexp'3 senv).
            assert (Q3 := H).
            apply T3 in Q3.
            destruct Q3.
            destruct H4.
            destruct H4.
            exists (Proc.If x x1 x3).
            exists (Lexical.If x0 x2 x4).
            simpl.
            rewrite -> H0.
            rewrite -> H2.
            rewrite -> H4.
            auto.

            exists (Proc.Var (nth senv l)).
            assert (T := find_index_some l H).
            destruct T.
            exists (Lexical.Var x).
            simpl.
            rewrite -> H0.
            auto.

            assert (T1 := IHexp'1 senv).
            assert (Q1 := H).
            apply T1 in Q1.
            destruct Q1.
            destruct H0.
            destruct H0.
            assert (T2 := IHexp'2 (Extend (generate_string (S ctx)) senv)).
            assert (Extend (generate_string (S ctx)) senv = generate (S ctx)).
                simpl.
                rewrite -> H.
                auto.
            apply T2 in H2.
            destruct H2.
            destruct H2.
            destruct H2.
            exists (Proc.Let (generate_string (S ctx)) x x1).
            exists (Lexical.Let x0 x2).
            rewrite translation_of_equation.
            rewrite -> H0.
            rewrite -> H2.
            auto.

            assert (T1 := IHexp' (Extend (generate_string (S ctx)) senv)).
            assert (Extend (generate_string (S ctx)) senv = generate (S ctx)).
                simpl.
                rewrite -> H.
                auto.
            apply T1 in H0.
            destruct H0.
            destruct H0.
            destruct H0.
            exists (Proc.Proc (generate_string (S ctx)) x).
            exists (Lexical.Proc x0).
            rewrite translation_of_equation.
            rewrite -> H0.
            auto.

            assert (T1 := IHexp'1 senv).
            assert (Q1 := H).
            apply T1 in Q1.
            destruct Q1.
            destruct H0.
            destruct H0.
            assert (T2 := IHexp'2 senv).
            assert (Q2 := H).
            apply T2 in Q2.
            destruct Q2.
            destruct H2.
            destruct H2.
            exists (Proc.Call x x1).
            exists (Lexical.Call x0 x2).
            simpl.
            rewrite -> H0.
            rewrite -> H2.
            auto.
    Qed.

    Lemma proc_val_construction : forall val', exists val, proc_val_lexical_val_rel val val'.
        intros.
        apply (Lexical.expval_mut
            (fun (val' : Lexical.expval) => exists val,
                proc_val_lexical_val_rel val val')
            (fun {ctx : nat} (env' : Lexical.environment ctx) => forall (senv : static_environment ctx), exists env,
                proc_env_static_env_rel env senv /\ proc_env_lexical_env_rel env env')); intros; eauto.

        assert (T := H (generate ctx)).
        destruct T.
        destruct H0.
        assert (Extend (generate_string (S ctx)) (generate ctx) = generate (S ctx)).
            simpl.
            auto.
        assert (T := proc_exp_construction e H2).
        destruct T.
        destruct H3.
        destruct H3.
        exists (Proc.Clo (generate_string (S ctx)) x0 x).
        eauto.

        dependent destruction senv.
        eauto.

        dependent destruction senv.
        specialize (H0 senv).
        destruct H0.
        destruct H0.
        destruct H.
        eauto.
    Qed.

    Lemma proc_env_construction : forall ctx (env' : Lexical.environment ctx) (senv : static_environment ctx), exists env, proc_env_static_env_rel env senv /\ proc_env_lexical_env_rel env env'.
        dependent induction env'; intros.
            dependent destruction senv.
            eauto.

            dependent destruction senv.
            specialize (IHenv' senv).
            destruct IHenv'.
            destruct H.
            assert (T := proc_val_construction e).
            destruct T.
            eauto.
    Qed.

    Hint Resolve proc_val_construction proc_env_construction proc_exp_construction.

    Lemma translation_of_soundness_generalized : forall ctx exp (senv : static_environment ctx) exp' env' val' env, translation_of exp senv = Some exp' -> Lexical.value_of_rel exp' env' val' -> proc_env_static_env_rel env senv -> proc_env_lexical_env_rel env env' -> exists val, proc_val_lexical_val_rel val val' /\ Proc.value_of_rel exp env val.
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

            admit.

            admit.

            admit.

            apply translation_of_var_inversion in H0.
            destruct H0.
            destruct H0.
            destruct H0.
            subst.
            admit.
    Admitted.

    Theorem translation_of_soundness : forall exp exp' val', translation_of exp Empty = Some exp' -> Lexical.value_of_rel exp' Lexical.Empty val' -> exists val, proc_val_lexical_val_rel val val' /\ Proc.value_of_rel exp Proc.Empty val.
        intros; eapply translation_of_soundness_generalized; eauto.
    Qed.

    Lemma translation_of_completeness_generalized : forall ctx (senv : static_environment ctx) env env' exp exp' val val', translation_of exp senv = Some exp' ->  proc_val_lexical_val_rel val val' -> proc_env_static_env_rel env senv -> proc_env_lexical_env_rel env env' -> Proc.value_of_rel exp env val -> Lexical.value_of_rel exp' env' val'.
    Admitted.

    Theorem translation_of_completeness : forall exp exp' val val', translation_of exp Empty = Some exp' -> proc_val_lexical_val_rel val val' -> Proc.value_of_rel exp Proc.Empty val -> Lexical.value_of_rel exp' Lexical.Empty val'.
        intros; eapply translation_of_completeness_generalized; eauto.
    Qed.
End Translation.
