Require Import Bool ZArith Arith String List.
Set Implicit Arguments.

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

Definition environment (A : Type) := string -> option A.
Definition empty_env {A : Type} : environment A := (fun _ => None).
Definition extend_env {A : Type} (x : string) (v : A) (env : environment A) :=
    fun y => if string_dec x y then Some v else env y.

Inductive expval : Type :=
| Num : Z -> expval
| Bool : bool -> expval
| Clo : string -> expression -> environment expval -> expval
.

Inductive value_of_rel : expression -> environment expval -> expval -> Prop :=
| VConst : forall num env, value_of_rel (Const num) env (Num (Z.of_nat num))
| VDiff : forall exp1 exp2 num1 num2 env, value_of_rel exp1 env (Num num1) -> value_of_rel exp2 env (Num num2) -> value_of_rel (Diff exp1 exp2) env (Num (num1 - num2))
| VIsZero : forall exp1 num1 env, value_of_rel exp1 env (Num num1) -> value_of_rel (IsZero exp1) env (Bool (Z.eqb num1 0))
| VIfTrue : forall exp1 exp2 exp3 val2 env, value_of_rel exp1 env (Bool true) -> value_of_rel exp2 env val2 -> value_of_rel (If exp1 exp2 exp3) env val2
| VIfFalse : forall exp1 exp2 exp3 val3 env, value_of_rel exp1 env (Bool false) -> value_of_rel exp3 env val3 -> value_of_rel (If exp1 exp2 exp3) env val3
| VVar : forall var env val, env var = Some val -> value_of_rel (Var var) env val
| VLet : forall var exp1 body env val1 valb, value_of_rel exp1 env val1 -> value_of_rel body (extend_env var val1 env) valb -> value_of_rel (Let var exp1 body) env valb
| VProc : forall var body env, value_of_rel (Proc var body) env (Clo var body env)
| VCall : forall rator rand env var body saved_env rand_val valb, value_of_rel rator env (Clo var body saved_env) -> value_of_rel rand env rand_val -> value_of_rel body (extend_env var rand_val saved_env) valb -> value_of_rel (Call rator rand) env valb
.

Notation "x <- e1 ; e2" :=
    (match e1 with
    | None => None
    | Some x => e2
    end)
(right associativity, at level 60).

Function value_of (exp : expression) (env : environment expval) (fuel : nat) : option expval :=
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
            | Var var => env var
            | Let var exp1 body =>
                    val1 <- value_of exp1 env fuel';
                    value_of body (extend_env var val1 env) fuel'
            | Proc var body => Some (Clo var body env)
            | Call rator rand =>
                    rator_val <- value_of rator env fuel';
                    match rator_val with
                    | Clo var body saved_env =>
                            rand_val <- value_of rand env fuel';
                            value_of body (extend_env var rand_val saved_env) fuel'
                    | _ => None
                    end
            end
    end.

Lemma option_eq {T : Type} (p q : T) : Some p = Some q -> p = q.
    congruence.
Qed.

Hint Constructors value_of_rel.

Theorem value_of_soundness : forall exp env val, (exists fuel, value_of exp env fuel = Some val) -> value_of_rel exp env val.
    intros.
    destruct H as [ fuel H ].
    generalize dependent val.
    generalize dependent env.
    generalize dependent fuel.
    induction exp; intros; destruct fuel; try discriminate; simpl in H; eauto.
        apply option_eq in H. rewrite <- H. auto.

        destruct (value_of exp1 env fuel) eqn:?; try discriminate.
        specialize (IHexp1 fuel env e).
        destruct (value_of exp2 env fuel) eqn:?; try discriminate.
        specialize (IHexp2 fuel env e0).
        destruct e eqn:?; try discriminate.
        destruct e0 eqn:?; try discriminate.
        apply option_eq in H. rewrite <- H. auto.

        destruct (value_of exp env fuel) eqn:?; try discriminate.
        specialize (IHexp fuel env e).
        destruct e eqn:?; try discriminate.
        apply option_eq in H. rewrite <- H. auto.

        destruct (value_of exp1 env fuel) eqn:?; try discriminate.
        specialize (IHexp1 fuel env e).
        destruct e; try discriminate.
        destruct b. specialize (IHexp2 fuel env val). auto. specialize (IHexp3 fuel env val). auto.

        destruct (value_of exp1 env fuel) eqn:?; try discriminate.
        specialize (IHexp1 fuel env e).
        specialize (IHexp2 fuel (extend_env s e env) val). eauto.

        apply option_eq in H. rewrite <- H. auto.

        destruct (value_of exp1 env fuel) eqn:?; try discriminate.
        specialize (IHexp1 fuel env e).
        destruct e; try discriminate.
        destruct (value_of exp2 env fuel) eqn:?; try discriminate.
        specialize (IHexp2 fuel env e1).
Admitted.

Lemma fuel_greater_than_zero : forall exp env fuel val, value_of exp env fuel = Some val -> fuel > O.
    intros.
    destruct fuel; try omega; discriminate.
Qed.

Lemma fuel_partial_order : forall exp env fuel val, value_of exp env fuel = Some val -> value_of exp env (S fuel) = Some val.
    intros.
    generalize dependent val.
    generalize dependent env.
    generalize dependent fuel.
    induction exp; intros; destruct fuel; try discriminate; simpl in H; eauto.
        destruct (value_of exp1 env fuel) eqn:?; try discriminate.
        specialize (IHexp1 fuel env e).
        destruct (value_of exp2 env fuel) eqn:?; try discriminate.
        specialize (IHexp2 fuel env e0).
        destruct e eqn:?; try discriminate.
        destruct e0 eqn:?; try discriminate.
        apply option_eq in H. rewrite <- H.
        apply IHexp1 in Heqo.
        apply IHexp2 in Heqo0.
        rewrite value_of_equation.
        rewrite -> Heqo.
        rewrite -> Heqo0.
        auto.

        destruct (value_of exp env fuel) eqn:?; try discriminate.
        specialize (IHexp fuel env e).
        destruct e eqn:?; try discriminate.
        apply option_eq in H. rewrite <- H.
        apply IHexp in Heqo.
        rewrite value_of_equation.
        rewrite -> Heqo.
        auto.

        destruct (value_of exp1 env fuel) eqn:?; try discriminate.
        specialize (IHexp1 fuel env e).
        destruct e eqn:?; try discriminate.
        apply IHexp1 in Heqo.
        destruct b.
            specialize (IHexp2 fuel env val). apply IHexp2 in H. rewrite value_of_equation. rewrite -> Heqo. auto.
            specialize (IHexp3 fuel env val). apply IHexp3 in H. rewrite value_of_equation. rewrite -> Heqo. auto.

        destruct (value_of exp1 env fuel) eqn:?; try discriminate.
        specialize (IHexp1 fuel env e).
        apply IHexp1 in Heqo.
        specialize (IHexp2 fuel (extend_env s e env) val).
        apply IHexp2 in H.
        rewrite value_of_equation.
        rewrite -> Heqo.
        auto.

        destruct (value_of exp1 env fuel) eqn:?; try discriminate.
        specialize (IHexp1 fuel env e).
        apply IHexp1 in Heqo.
        destruct e eqn:?; try discriminate.
        destruct (value_of exp2 env fuel) eqn:?; try discriminate.
        specialize (IHexp2 fuel env e2).
        apply IHexp2 in Heqo0.
        rewrite value_of_equation.
        rewrite -> Heqo.
        rewrite -> Heqo0.
Admitted.

Theorem value_of_completeness : forall exp env val, value_of_rel exp env val -> exists fuel, value_of exp env fuel = Some val.
    intros.
    induction H.
        exists (S O); auto.

        destruct IHvalue_of_rel1 as [ fuel1 H1 ].
        destruct IHvalue_of_rel2 as [ fuel2 H2 ].
        exists (S (max fuel1 fuel2)).
Abort.

Theorem value_of_correctness : forall exp env val, (exists fuel, value_of exp env fuel = Some val) <-> value_of_rel exp env val.
Abort.
