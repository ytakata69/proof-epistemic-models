(*
 * Definitions & properties of transitive closures
 *)

Require Import Sets.Ensembles.

Section TransitiveClosures.

Variable A : Type.
Variable R : A -> Ensemble A.

Inductive transClosure : A -> Ensemble A :=
| tc_base : forall (a : A),
    Included _ (R a) (transClosure a)
| tc_trans : forall (a b c : A),
    In _ (transClosure a) b -> In _ (transClosure b) c
    -> In _ (transClosure a) c
.

Inductive tcHeadTail : A -> Ensemble A :=
| tc_ht_base : forall (a : A),
    Included _ (R a) (tcHeadTail a)
| tc_ht_trans : forall (a b c : A),
    In _ (R a) b -> In _ (tcHeadTail b) c
    -> In _ (tcHeadTail a) c
.

Inductive tcInitLast : A -> Ensemble A :=
| tc_il_base : forall (a : A),
    Included _ (R a) (tcInitLast a)
| tc_il_trans : forall (a b c : A),
    In _ (tcInitLast a) b -> In _ (R b) c
    -> In _ (tcInitLast a) c
.

Theorem tcHeadTail_equals_tc :
  forall a, tcHeadTail a = transClosure a.
Proof.
  intros a.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split; intros x Hax.
  - (* to show ⊆ *)
  induction Hax as [a x Hax
    | a b x Hax Hbx IH].
  + (* when tc_ht_base *)
  now apply tc_base.
  + (* when tc_ht_trans *)
  apply tc_trans with (b:=b);
  [| assumption].
  now apply tc_base.
  - (* to show ⊇ *)
  induction Hax as [a x Hax
    | a b x Hab Hht_ab Hbx IH].
  + (* when tc_base *)
  now apply tc_ht_base.
  + (* when tc_trans *)
  clear Hab Hbx.
  induction Hht_ab as [a b Hab
    | a b c Hab Hbc IHab].
  * (* when b ∈ R a /\ x ∈ tcHeadTail b *)
  now apply tc_ht_trans with (b:=b).
  * (* when b ∈ R a /\ c ∈ tcHeadTail b /\ x ∈ tcHeadTail c *)
  apply tc_ht_trans with (b:=b);
  [assumption |].
  apply IHab; apply IH.
Qed.

Theorem tcInitLast_equals_tc :
  forall a, tcInitLast a = transClosure a.
Proof.
  intros a.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split; intros x Hax.
  - (* to show ⊆ *)
  induction Hax as [a x Hax
    | a b x Hax Hbx IH].
  + (* when tc_il_base *)
  now apply tc_base.
  + (* when tc_il_trans *)
  apply tc_trans with (b:=b);
  [assumption |].
  now apply tc_base.
  - (* to show ⊇ *)
  induction Hax as [a x Hax
    | a b x Hab Hil_ab Hbx IH].
  + (* when tc_base *)
  now apply tc_il_base.
  + (* when tc_trans *)
  clear Hab Hbx.
  induction IH as [b x Hbx
    | b c x Hbc IHac Hcx].
  * (* when b ∈ tcInitLast a /\ x ∈ R b *)
  now apply tc_il_trans with (b:=b).
  * (* when b ∈ tcInitLast a /\ c ∈ tcInitLast b /\ x ∈ R c *)
  apply tc_il_trans with (b:=c);
  [| assumption].
  apply IHac; apply Hil_ab.
Qed.

Theorem tcHeadTail_equals_tcInitLast :
  forall a, tcHeadTail a = tcInitLast a.
Proof.
  intros a.
  rewrite tcInitLast_equals_tc.
  apply tcHeadTail_equals_tc.
Qed.

End TransitiveClosures.
