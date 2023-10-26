(*
 * Proofs on epistemic models
 *)

Require Import Arith.
Require Import Sets.Ensembles.

Section Preliminaries.

Fixpoint fpow {A : Type} (f : A -> A) (n : nat) : A -> A :=
  match n with
  | O => fun x => x
  | S n' => fun x => f (fpow f n' x)
  end.

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

Hypothesis K_is_KD45 : isKD45 K.

Lemma same_R_p :
  forall (p : P) (w w' : W),
  In _ (R p w) w' -> R p w = R p w'.
Proof.
  destruct K_is_KD45 as [_ [Htra Heuc]].
  unfold transitive in Htra.
  unfold euclidean in Heuc.

  intros p w w' Hin.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split;
  unfold Included;
  intros x Hx.
  - (* to show R p w ⊆ R p w' *)
  now apply Heuc with (w:=w).
  - (* to show R p w' ⊆ R p w *)
  now apply Htra with (w':=w').
Qed.

(* E is a predicate on W and E w depends only on R p w *)
Definition PredicateOnRp (p : P) (E : Ensemble W) : Prop :=
  forall (w w' : W),
  R p w = R p w' ->
    (In _ E w <-> In _ E w').

Lemma PredicateOnRp_transitivity :
  forall (p : P) (E : Ensemble W),
    PredicateOnRp p E ->
  forall (w1 w2 : W),
    In _ (R p w1) w2 ->
    (In _ E w1 <-> In _ E w2).
Proof.
  intros p E Hpred w1 w2 H12.
  unfold PredicateOnRp in Hpred.
  apply Hpred.
  now apply same_R_p.
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

Lemma Rplus_singleton_equals_R_p :
  forall (p : P) (w : W),
  Rplus (Singleton _ p) w = R p w.
Proof.
  intros p w.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split;
  unfold Included;
  intros x Hx.
  - (* to show ⊆ *)
  induction Hx as [p' w' Hpp' x Hx
    | p' w' x y Hpp' Hx Hxy IH];
  inversion Hpp' as [EQp];
  rewrite <- EQp in Hx;
  rewrite <- EQp;
  clear p' EQp Hpp'.
  + (* when Rplus_base *)
  apply Hx.
  + (* when Rplus_trans *)
  destruct K_is_KD45 as [_ [Htra _]].
  unfold transitive in Htra.
  now apply Htra with (w':=x).
  - (* to show ⊇ *)
  generalize dependent x.
  apply Rplus_base.
  apply In_singleton.
Qed.

Lemma CB_p_equals_B_p :
  forall (p : P) (E : Ensemble W),
  CB (Singleton _ p) E = B p E.
Proof.
  intros p E.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split;
  unfold Included;
  intros w Hw.
  - (* to show ⊆ *)
  inversion Hw as [w' HRP EQw'];
  clear w' EQw' Hw.
  rewrite Rplus_singleton_equals_R_p in HRP.
  now apply B_intro.
  - (* to show ⊇ *)
  inversion Hw as [w' Hw' EQw'];
  clear w' EQw' Hw.
  apply CB_intro.
  now rewrite Rplus_singleton_equals_R_p.
Qed.

Lemma B_p_is_idempotent :
  forall (p : P) (E : Ensemble W),
  B p E = B p (B p E).
Proof.
  destruct K_is_KD45 as [Hser [Htra Heuc]].

  intros p E.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split;
  unfold Included;
  intros x Hx;
  inversion Hx as [x' Hx' EQx'];
  clear x' EQx' Hx.
  - (* to show ⊆ *)
  unfold transitive in Htra.

  apply B_intro.
  unfold Included.
  intros y Hy.
  apply B_intro.
  unfold Included.
  intros z Hz.
  apply Hx'.
  now apply Htra with (w':=y).

  - (* to show ⊇ *)
  unfold serial in Hser.
  unfold euclidean in Heuc.
  destruct (Hser p x) as [x' Hxx'].
  specialize (Hx' _ Hxx').
  specialize (Heuc _ _ _ Hxx').

  apply B_intro.
  unfold Included.
  intros y Hy.
  inversion Hx' as [x'' Hx'E EQx''];
  clear x'' EQx'' Hx'.
  apply Hx'E.
  now apply Heuc.
Qed.

Lemma B_p_equals_pow_B_p :
  forall (p : P) (E : Ensemble W) (n : nat),
  n > 0 -> B p E = fpow (B p) n E.
Proof.
  intros p E n Hn.
  destruct n as [| m];
  [inversion Hn |];
  clear Hn.
  induction m as [| m IHm].
  - (* when m = 0 *)
  unfold fpow.
  reflexivity.
  - (* when m > 0 *)
  remember (S m) as n eqn:EQn.
  unfold fpow.
  unfold fpow in IHm.
  rewrite <- IHm.
  apply B_p_is_idempotent.
Qed.

Theorem PredicateOnRp_is_fixpoint_of_B :
  forall (p : P) (E : Ensemble W),
  PredicateOnRp _ p E -> E = B p E.
Proof.
  intros p E Hpred.
  unfold PredicateOnRp in Hpred.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  - (* to show E ⊆ B p E *)
  unfold Included.
  intros w Hi.
  apply B_intro.
  unfold Included.
  intros x Hix.
  specialize (Hpred w x).
  apply same_R_p in Hix;
  [| apply K_is_KD45].
  now apply (Hpred Hix).
  - (* to show B p E ⊆ E *)
  unfold Included.
  intros w HiB.
  inversion HiB as [w' Hi EQw'];
  clear w' EQw' HiB.

  destruct K_is_KD45 as [Hser _].
  unfold serial in Hser.
  specialize (Hser p w).
  destruct Hser as [w' Hw'].

  unfold Included in Hi.
  specialize (Hi w' Hw').
  apply same_R_p in Hw';
  [| apply K_is_KD45].

  now apply (Hpred _ _ Hw').
Qed.

End BeliefOperators.

Section EpistemicModels.

Definition P := nat.  (* players *)

Variable strategy : Set.
Definition StrProf := P -> strategy.
Definition StrProfMap (K : Frame P) := W -> StrProf.

Definition isEpistemicModel (K : Frame P) (sigma : StrProfMap K) : Prop :=
  forall (p : P) (w w' : W),
    In _ (R p w) w' -> sigma w p = sigma w' p.

Lemma weak_definition_of_EM :
  forall (K : Frame P) (sigma : StrProfMap K),
    isKD45 K ->
    isEpistemicModel sigma ->
  forall (p : P) (w w1 w2 : W),
    In _ (R p w) w1 -> In _ (R p w) w2 ->
    sigma w1 p = sigma w2 p.
Proof.
  intros K sigma K_is_KD45 HEM
    p w w1 w2 H1 H2.
  apply HEM.
  destruct K_is_KD45 as [_ [_ Heuc]].
  now apply Heuc with (w:=w).
Qed.

Definition update (s : StrProf) (p : P) (sp : strategy) : StrProf :=
  fun q => if p =? q then sp else s q.

Variable win : StrProf -> P -> Prop.
Variable K : Frame P.
Variable sigma : StrProfMap K.

Definition keepWinning (p : P) (w' : W) (sp' : strategy) : Prop :=
  win (sigma w') p -> win (update (sigma w') p sp') p.
Definition profitableDev (p : P) (w' : W) (sp' : strategy) : Prop :=
  ~ win (sigma w') p /\ win (update (sigma w') p sp') p.

Definition isRational (p : P) (w : W) : Prop :=
  forall sp' : strategy,
  (exists w' : W, In _ (R p w) w' /\
    ~ keepWinning p w' sp') \/
  (forall w' : W, In _ (R p w) w' ->
    ~ profitableDev p w' sp').

Inductive RAT (p : P) : Ensemble W :=
| RAT_intro :
    forall w : W, isRational p w
      -> In _ (RAT p) w.

Lemma isRational_is_PredicateOnRp :
  forall p, PredicateOnRp _ p (isRational p).
Proof.
  intros p.
  unfold PredicateOnRp.
  intros w w' Heq.
  split;
  unfold isRational, In;
  intros H;
  intros sp'; specialize (H sp').
  - (* to show -> *)
  rewrite <- Heq.
  destruct H as [H | H];
  [left | right].
  + destruct H as [w1 H];
  now exists w1.
  + apply H.
  - (* to show <- *)
  rewrite Heq.
  destruct H as [H | H];
  [left | right].
  + destruct H as [w1 H];
  now exists w1.
  + apply H.
Qed.

Lemma RAT_is_PredicateOnRp :
  forall p, PredicateOnRp _ p (RAT p).
Proof.
  unfold PredicateOnRp.
  intros p w w' Heq.
  apply isRational_is_PredicateOnRp in Heq.
  unfold In in Heq.
  split;
  intros H;
  apply RAT_intro;
  inversion H as [x Hr EQx];
  clear x EQx;
  now apply Heq.
Qed.

Hypothesis K_is_KD45 : isKD45 K.

Lemma RAT_transitivity :
  forall (p : P) (w1 w2 : W),
  In _ (R p w1) w2 ->
  (In _ (RAT p) w1 <-> In _ (RAT p) w2).
Proof.
  intros p w1 w2.
  apply PredicateOnRp_transitivity;
  [assumption |].
  apply RAT_is_PredicateOnRp.
Qed.

Theorem RAT_is_fixpoint_of_B :
  forall p : P, RAT p = B _ p (RAT p).
Proof.
  intros p.
  apply PredicateOnRp_is_fixpoint_of_B;
  [assumption |].
  apply RAT_is_PredicateOnRp.
Qed.

Theorem RAT_equals_pow_B_RAT :
  forall (p : P) (n : nat), RAT p = fpow (B _ p) n (RAT p).
Proof.
  intros p n.
  induction n as [| n IHn].
  - (* when n = 0 *)
  unfold fpow.
  reflexivity.
  - (* when n > 0 *)
  unfold fpow.
  unfold fpow in IHn.
  rewrite <- IHn.
  apply RAT_is_fixpoint_of_B.
Qed.

Theorem RAT_equals_CB_RAT :
  forall p : P,
    RAT p = CB _ (Singleton _ p) (RAT p).
Proof.
  intros p.
  rewrite CB_p_equals_B_p;
  [| assumption].
  apply RAT_is_fixpoint_of_B.
Qed.

Hypothesis K_sigma_is_EM : isEpistemicModel sigma.


End EpistemicModels.
