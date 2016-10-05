Require Import Bool ZArith Arith String List.
Set Implicit Arguments.

Inductive expression : Set :=
| Const : nat -> expression
| Diff : expression -> expression -> expression
| IsZero : expression -> expression
| If : expression -> expression -> expression -> expression
| Var : string -> expression
| Let : string -> expression -> expression -> expression
.

Inductive expval : Set :=
| Num : Z -> expval
| Bool : bool -> expval
.

Definition environment := string -> option expval.
Definition empty_env : environment := (fun _ => None).
Definition extend_env (x : string) (v : expval) (env : environment) :=
    fun y => if string_dec x y then Some v else env y.

Inductive value_of_rel : expression -> environment -> expval -> Prop :=
| VConst : forall num env, value_of_rel (Const num) env (Num (Z.of_nat num))
| VDiff : forall exp1 exp2 num1 num2 env, value_of_rel exp1 env (Num num1) -> value_of_rel exp2 env (Num num2) -> value_of_rel (Diff exp1 exp2) env (Num (num1 - num2))
| VIsZero : forall exp1 num1 env, value_of_rel exp1 env (Num num1) -> value_of_rel (IsZero exp1) env (Bool (Z.eqb num1 0))
| VIfTrue : forall exp1 exp2 exp3 val2 env, value_of_rel exp1 env (Bool true) -> value_of_rel exp2 env val2 -> value_of_rel (If exp1 exp2 exp3) env val2
| VIfFalse : forall exp1 exp2 exp3 val3 env, value_of_rel exp1 env (Bool false) -> value_of_rel exp3 env val3 -> value_of_rel (If exp1 exp2 exp3) env val3
| VVar : forall var env val, env var = Some val -> value_of_rel (Var var) env val
| VLet : forall var exp1 body env val1 valb, value_of_rel exp1 env val1 -> value_of_rel body (extend_env var val1 env) valb -> value_of_rel (Let var exp1 body) env valb
.

Notation "x <- e1 ; e2" :=
    (match e1 with
    | None => None
    | Some x => e2
    end)
(right associativity, at level 60).

Fixpoint value_of (exp : expression) (env : environment) : option expval :=
    match exp with
    | Const num => Some (Num (Z.of_nat num))
    | Diff exp1 exp2 =>
            val1 <- value_of exp1 env;
            val2 <- value_of exp2 env;
            match (val1, val2) with
            | (Num num1, Num num2) => Some (Num (num1 - num2))
            | _ => None
            end
    | IsZero exp1 =>
            val1 <- value_of exp1 env;
            match val1 with
            | Num num1 => Some (Bool (Z.eqb num1 0))
            | _ => None
            end
    | If exp1 exp2 exp3 =>
            val1 <- value_of exp1 env;
            match val1 with
            | Bool true => value_of exp2 env
            | Bool false => value_of exp3 env
            | _ => None
            end
    | Var var => env var
    | Let var exp1 body =>
            val1 <- value_of exp1 env;
            value_of body (extend_env var val1 env)
    end.

Lemma option_eq {T : Type} (p q : T) : Some p = Some q -> p = q.
    congruence.
Qed.

Hint Constructors value_of_rel.

Theorem value_of_soundness : forall exp env val, value_of exp env = Some val -> value_of_rel exp env val.
    intros.
    generalize dependent val.
    generalize dependent env.
    induction exp; intros; eauto; simpl in H.
        apply option_eq in H. rewrite <- H. auto.

        destruct (value_of exp1 env) eqn:?; try discriminate.
        specialize (IHexp1 env e). destruct (value_of exp2 env) eqn:?; try discriminate.
        specialize (IHexp2 env e0). destruct e; try discriminate.
        destruct e0; try discriminate.
        apply option_eq in H. rewrite <- H. auto.

        destruct (value_of exp env) eqn:?; try discriminate.
        specialize (IHexp env e). destruct e; try discriminate.
        apply option_eq in H. rewrite <- H. auto.

        destruct (value_of exp1 env) eqn:?; try discriminate.
        specialize (IHexp1 env e). destruct e; try discriminate.
        destruct b; auto.

        destruct (value_of exp1 env) eqn:?; try discriminate.
        specialize (IHexp1 env e). specialize (IHexp2 (extend_env s e env) val). eauto.
Qed.

Theorem value_of_completeness : forall exp env val, value_of_rel exp env val -> value_of exp env = Some val.
    intros.
    induction H; simpl; eauto.
        rewrite -> IHvalue_of_rel1. rewrite -> IHvalue_of_rel2. auto.
        rewrite -> IHvalue_of_rel. auto.
        rewrite -> IHvalue_of_rel1. auto.
        rewrite -> IHvalue_of_rel1. auto.
        rewrite -> IHvalue_of_rel1. auto.
Qed.

Theorem value_of_correctness : forall exp env val, value_of exp env = Some val <-> value_of_rel exp env val.
    intros.
    split.
        apply value_of_soundness.
        apply value_of_completeness.
Qed.
