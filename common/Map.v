Require Import Classical ClassicalEpsilon FunctionalExtensionality.
Set Implicit Arguments.

Module Type S.
  Parameter fmap : Type -> Type -> Type.

  Parameter empty : forall K V, fmap K V.
  Parameter lookup : forall K V, fmap K V -> K -> option V.
  Parameter add : forall K V, fmap K V -> K -> V -> fmap K V.

  Notation "$0" := (empty _ _).
  Notation "m $+ ( k , v )" := (add m k v) (left associativity, at level 50).
  Infix "$?" := lookup (no associativity, at level 50).

  Axiom fmap_ext :
    forall K V (m1 m2 : fmap K V),
      (forall k, m1 $? k = m2 $? k) ->
      m1 = m2.

  Axiom lookup_empty : forall K V k, (empty K V) $? k = None.

  Axiom lookup_add_eq :
    forall K V (m : fmap K V) k1 k2 v,
      k1 = k2 ->
      m $+ (k1, v) $? k2 = Some v.

  Axiom lookup_add_ne :
    forall K V (m : fmap K V) k k' v,
      k' <> k ->
      m $+ (k, v) $? k' = m $? k'.

  Hint Extern 1 => match goal with
                  | [ H : lookup (empty _ _) _ = Some _ |- _ ] =>
                    rewrite lookup_empty in H; discriminate
                  end.

  Hint Rewrite lookup_empty lookup_add_eq lookup_add_ne using congruence.

  Ltac maps_equal :=
    apply fmap_ext; intros;
    repeat (subst; autorewrite with core; try trivial;
            match goal with
            | [ |- context[lookup (add _ ?k _) ?k'] ] => destruct (classic (k = k')); subst
            end).

  Hint Extern 3 (_ = _) => maps_equal.
End S.

Module M : S.
  Definition fmap (K V : Type) := K -> option V.

  Definition empty K V : fmap K V := fun _ => None.

  Section decide.
    Variable P : Prop.

    Definition decide := excluded_middle_informative P.
  End decide.

  Definition add K V (m : fmap K V) k v : fmap K V:=
    fun k' => if decide (k' = k) then Some v else m k'.
  Definition lookup K V (m : fmap K V) k := m k.

  Theorem fmap_ext :
    forall K V (m1 m2 : fmap K V),
      (forall k, lookup m1 k = lookup m2 k) ->
      m1 = m2.
  Proof.
    intros.
    extensionality k.
    auto.
  Qed.

  Theorem lookup_empty : forall K V (k : K), lookup (empty V) k = None.
    auto.
  Qed.

  Theorem lookup_add_eq :
    forall K V (m : fmap K V) k1 k2 v,
      k1 = k2 ->
      lookup (add m k1 v) k2 = Some v.
  Proof.
    unfold lookup, add.
    intros.
    destruct (decide (k2 = k1)); congruence.
  Qed.

  Theorem lookup_add_ne :
    forall K V (m : fmap K V) k k' v,
      k' <> k ->
      lookup (add m k v) k' = lookup m k'.
  Proof.
    unfold lookup, add.
    intros.
    destruct (decide (k' = k)); congruence.
  Qed.
End M.

Export M.