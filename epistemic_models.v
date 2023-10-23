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

Lemma CB_is_included_by_pow_B :
  forall (p : P) (E : Ensemble W) (n : nat),
  n > 0 ->
  Included _ (CB (Singleton _ p) E) (fpow (B p) n E).
Proof.
  intros p E n Hnpos.
  destruct n as [| m].
  - (* when n = 0 *)
  inversion Hnpos.

  - (* when n = S m *)
  clear Hnpos.
  induction m as [| m IHm];
  unfold Included;
  intros x HCBx;
  inversion HCBx as [w' HRPx EQw'];
  clear w' EQw' HCBx;
  unfold Included in HRPx;
  unfold fpow;
  apply B_intro;
  unfold Included;
  intros y HRxy.
  + (* when m = 0 *)
  apply HRPx.
  apply Rplus_base with (H:=Singleton _ p) in HRxy;
  [apply HRxy | apply In_singleton].
  + (* when m > 0 *)
  unfold Included in IHm.
  apply IHm.
  apply CB_intro.
  unfold Included.
  intros z HRPz.
  apply HRPx.
  apply Rplus_trans with (p:=p) (w2:=y);
  [apply In_singleton | apply HRxy | apply HRPz].
Qed.

Definition posnat (n : nat) : Prop := n > 0.

Lemma CB_is_included_by_intersection_of_pow_B :
  forall (p : P) (E : Ensemble W),
  Included _ (CB (Singleton _ p) E)
    (IntersectionForall posnat (fun n => fpow (B p) n E)).
Proof.
  intros p E.
  unfold Included.
  intros x HCBx.
  apply IntersectionForall_intro.
  intros n Hn.
  destruct Hn as [| m];
  generalize dependent x;
  apply CB_is_included_by_pow_B;
  apply Nat.lt_0_succ.
Qed.

Lemma CB_includes_intersection_of_pow_B :
  forall (p : P) (E : Ensemble W),
  Included _
    (IntersectionForall posnat (fun n => fpow (B p) n E))
    (CB (Singleton _ p) E).
Proof.
  intros p E.
  unfold Included.
  intros x HIBx.
  inversion HIBx as [x' HIBx' EQx'];
  clear x' EQx' HIBx.

  apply CB_intro.
  unfold Included.
  intros y HRPxy.
  generalize dependent HIBx'.
  induction HRPxy as [p' w' Hpp' x' HRw'x'
    | p' w' x' y' Hpp' HRw'x' HRPx'y' IH];
  inversion Hpp' as [EQp];
  rewrite <- EQp in HRw'x';
  rewrite <- EQp;
  clear p' EQp Hpp';
  intros HIBw'.

  - (* when Rplus_base *)
  assert (Hpos1 : In _ posnat 1).
  { unfold In, posnat. apply Nat.lt_0_succ. }
  specialize (HIBw' 1 Hpos1);
  clear Hpos1;
  unfold fpow in HIBw'.
  inversion HIBw' as [w Hw' EQw];
  clear w EQw HIBw'.
  now apply Hw'.
  - (* when Rplus_trans *)
  apply IH.
  intros n Hn.
  specialize (HIBw' n Hn).
  destruct n as [| m].
  + (* when n = 0 *)
  inversion Hn.
  + (* when n = S m *)
  clear Hn IH HRPx'y'.
  destruct K_is_KD45 as [_ [Htra _]].
  unfold transitive in Htra.

  inversion HIBw' as [w Hw' EQw];
  clear w EQw HIBw'.
  apply B_intro.
  unfold Included.
  intros z HRx'z.
  apply Hw'.
  now apply Htra with (w':=x').
Qed.

Lemma CB_equals_intersection_of_pow_B :
  forall (p : P) (E : Ensemble W),
  CB (Singleton _ p) E =
    IntersectionForall posnat (fun n => fpow (B p) n E).
Proof.
  intros p E.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  - apply CB_is_included_by_intersection_of_pow_B.
  - apply CB_includes_intersection_of_pow_B.
Qed.

End BeliefOperators.

Section EpistemicModels.

Definition P := nat.  (* players *)

Variable strategy : Set.
Definition StrProf := P -> strategy.
Definition StrProfMap (K : Frame P) := W -> StrProf.

Definition isEpistemicModel (K : Frame P) (sigma : StrProfMap K) : Prop :=
  forall (p : P) (w w1 w2 : W),
    In _ (R p w) w1 -> In _ (R p w) w2 ->
    sigma w1 p = sigma w2 p.

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

Hypothesis K_is_KD45 : isKD45 K.

Lemma RAT_transitivity :
  forall (p : P) (w1 w2 : W),
  In _ (R p w1) w2 ->
  (In _ (RAT p) w1 <-> In _ (RAT p) w2).
Proof.
  destruct K_is_KD45 as [_ [Htra Heuc]].
  unfold transitive in Htra.
  unfold Included in Htra.
  unfold euclidean in Heuc.
  unfold Included in Heuc.

  intros p w1 w2 H12.
  split; intros H1;
  apply RAT_intro;
  inversion H1 as [x Hrat EQx];
  clear x EQx H1;
  unfold isRational;
  unfold isRational in Hrat;
  intros sp';
  specialize (Hrat sp');
  destruct Hrat as [Hrat | Hrat];
  [left | right | left | right].

  - (* to show w1 ∈ RAT p -> w2 ∈ RAT p *)
    (* case 1 of isRational p w2 *)
  destruct Hrat as [w' [Hi Hrat]].
  exists w'.
  split; [| assumption].
  now apply Heuc with (w:=w1).
  - (* case 2 of isRational p w2 *)
  intros w' Hi.
  apply Hrat.
  now apply Htra with (w':=w2).

  - (* to show w2 ∈ RAT p -> w1 ∈ RAT p *)
    (* case 1 of isRational p w1 *)
  destruct Hrat as [w' [Hi Hrat]].
  exists w'.
  split; [| assumption].
  now apply Htra with (w':=w2).
  - (* case 2 of isRational p w1 *)
  intros w' Hi.
  apply Hrat.
  now apply Heuc with (w:=w1).
Qed.

Theorem RAT_is_fixpoint_of_B :
  forall p : P, RAT p = B _ p (RAT p).
Proof.
  intros p.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  - (* to show RAT p ⊆ B _ p (RAT p) *)
  unfold Included.
  intros w Hi.
  apply B_intro.
  unfold Included.
  intros x Hix.
  now apply RAT_transitivity with (w1:=w).
  - (* to show B _ p (RAT p) ⊆ RAT p *)
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
  now apply RAT_transitivity with (w2:=w').
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
  rewrite CB_equals_intersection_of_pow_B;
  [| apply K_is_KD45].
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  - (* to show RAT p ⊆ ∩_n (B p)^n (RAT p) *)
  unfold Included.
  intros x Hx.
  apply IntersectionForall_intro.
  intros n Hn.
  now rewrite <- RAT_equals_pow_B_RAT.
  - (* to show ∩_n (B p)^n (RAT p) ⊆ RAT p *)
  unfold Included.
  intros x Hax.
  inversion Hax as [x' Hx EQx'];
  clear x' EQx' Hax.
  rewrite RAT_equals_pow_B_RAT with (n:=1).
  apply Hx.
  unfold In, posnat.
  apply Nat.lt_0_succ.
Qed.

Hypothesis K_sigma_is_EM : isEpistemicModel sigma.


End EpistemicModels.
