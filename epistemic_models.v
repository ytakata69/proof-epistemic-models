(*
 * Proofs on epistemic models
 *)

Require Import Sets.Ensembles.

Section Preliminaries.

(* ∩_{x ∈ P} S(x) *)
Inductive IntersectionForall {X Y : Type}
  (P : Ensemble X) (S : X -> Ensemble Y) : Ensemble Y :=
| IntersectionForall_intro :
    forall y, (forall x, In _ P x -> In _ (S x) y) ->
      In _ (IntersectionForall P S) y.

End Preliminaries.

Section KripkeFrames.

Class Frame (P : Set) := mkFrame { (* P : players *)
  W : Set;  (* worlds *)
  R : P -> W -> Ensemble W;  (* relation *)
}.

Variable P : Set.  (* players *)
Set Implicit Arguments.

Definition serial (K : Frame P) : Prop :=
  forall (p : P) (w : W), exists w', In _ (R p w) w'.

Definition transitive (K : Frame P) : Prop :=
  forall (p : P) (w w' : W),
    In _ (R p w) w' -> Included _ (R p w') (R p w).

Definition euclidean (K : Frame P) : Prop :=
  forall (p : P) (w w' : W),
    In _ (R p w) w' -> Included _ (R p w) (R p w').

Definition reflexive (K : Frame P) : Prop :=
  forall (p : P) (w : W),
    In _ (R p w) w.

Definition symmetric (K : Frame P) : Prop :=
  forall (p : P) (w w' : W),
    In _ (R p w) w' -> In _ (R p w') w.

Definition isKD45 (K : Frame P) : Prop :=
  serial K /\ transitive K /\ euclidean K.

Definition isKT5 (K : Frame P) : Prop :=
  reflexive K /\ euclidean K.

Variable K : Frame P.

Lemma KT5_is_symmetric : isKT5 K -> symmetric K.
Proof.
  intros Hk.
  destruct Hk as [Href Heuc].
  unfold reflexive in Href.
  unfold euclidean in Heuc.
  unfold Included in Heuc.
  unfold symmetric.
  intros p w w' Hi.
  apply Heuc with w.
  - apply Hi.
  - apply Href.
Qed.

Lemma KT5_is_transitive : isKT5 K -> transitive K.
Proof.
  intros Hk.
  apply KT5_is_symmetric in Hk as Hs.
  unfold symmetric in Hs.
  destruct Hk as [Href Heuc].
  unfold reflexive in Href.
  unfold euclidean in Heuc.
  unfold Included in Heuc.
  unfold transitive.
  unfold Included.
  intros p w w' Hi x Hix.
  specialize (Heuc p w' w).
  apply Heuc.
  - now apply Hs.
  - apply Hix.
Qed.

Lemma KT5_is_serial : isKT5 K -> serial K.
Proof.
  intros Hk.
  destruct Hk as [Href _].
  unfold reflexive in Href.
  unfold serial.
  intros p w.
  exists w.
  apply Href.
Qed.

Lemma KT5_is_a_KD45 : isKT5 K -> isKD45 K.
Proof.
  intros Hk.
  unfold isKD45.
  split; [| split].
  - now apply KT5_is_serial.
  - now apply KT5_is_transitive.
  - now destruct Hk as [_ Heuc].
Qed.

End KripkeFrames.

Section BeliefOperators.

Variable P : Set.  (* players *)
Variable K : Frame P.  (* a Kripke frame *)

Inductive Rplus (H : Ensemble P) : W -> Ensemble W :=
| Rplus_base : forall (p : P) (w : W),
    In _ H p ->
    Included _ (R p w) (Rplus H w)
| Rplus_trans : forall (p : P) (w1 w2 w3 : W),
    In _ H p ->
    In _ (R p w1) w2 -> In _ (Rplus H w2) w3
    -> In _ (Rplus H w1) w3
.

Inductive B (p : P) (E : Ensemble W) : Ensemble W :=
| B_intro : forall w : W,
    Included _ (R p w) E -> In _ (B p E) w
.

Inductive CB (H : Ensemble P) (E : Ensemble W) : Ensemble W :=
| CB_intro : forall w : W,
    Included _ (Rplus H w) E -> In _ (CB H E) w
.

Inductive D (H : Ensemble P) (E : Ensemble W) : Ensemble W :=
| D_intro : forall w : W,
    Included _
      (IntersectionForall H (fun p => R p w)) E
    -> In _ (D H E) w
.

Hypothesis K_is_KD45 : isKD45 K.

End BeliefOperators.
