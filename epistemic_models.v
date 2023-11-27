(*
 * Proofs on epistemic models
 *)

Require Import Arith.
Require Import Sets.Ensembles.
Require Import trans_closures.

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

Inductive Rh (H : Ensemble P) : W -> Ensemble W :=
| Rh_intro : forall (p : P) (w : W),
    In _ H p -> Included _ (R p w) (Rh H w)
.
Inductive Rplus (H : Ensemble P) : W -> Ensemble W :=
| Rplus_intro : forall (w : W),
    Included _ (tcInitLast _ (Rh H) w) (Rplus H w)
.

Lemma Rplus_base :
  forall (H : Ensemble P) (p : P) (w : W),
    In _ H p ->
    Included _ (R p w) (Rplus H w).
Proof.
  intros H p w Hp x Hx.
  assert (H'x : In _ (tcInitLast _ (Rh H) w) x).
  { apply tc_il_base. generalize dependent x. now apply Rh_intro. }
  clear Hx.
  generalize dependent x.
  now apply Rplus_intro.
Qed.

Lemma Rplus_trans :
  forall (H : Ensemble P) (p : P) (w1 w2 w3 : W),
    In _ H p ->
    In _ (Rplus H w1) w2 -> In _ (R p w2) w3
    -> In _ (Rplus H w1) w3.
Proof.
  intros H p w1 w2 w3 Hp H12 H23.
  assert (H13 : In _ (tcInitLast _ (Rh H) w1) w3).
  {
    inversion H12 as [w x H'12 EQw EQx];
    clear w EQw x EQx.
    apply tc_il_trans with (b:=w2); [assumption |].
    generalize dependent w3.
    now apply Rh_intro.
  }
  clear H23.
  generalize dependent w3.
  apply Rplus_intro.
Qed.

(*
Inductive Rplus (H : Ensemble P) : W -> Ensemble W :=
| Rplus_base : forall (p : P) (w : W),
    In _ H p ->
    Included _ (R p w) (Rplus H w)
| Rplus_trans : forall (p : P) (w1 w2 w3 : W),
    In _ H p ->
    In _ (Rplus H w1) w2 -> In _ (R p w2) w3
    -> In _ (Rplus H w1) w3
.
*)

(* another definition *)
(*
Inductive Rplus' (H : Ensemble P) : W -> Ensemble W :=
| Rplus'_base : forall (p : P) (w : W),
    In _ H p ->
    Included _ (R p w) (Rplus' H w)
| Rplus'_trans : forall (p : P) ( w1 w2 w3 : W),
    In _ H p ->
    In _ (R p w1) w2 -> In _ (Rplus' H w2) w3
    -> In _ (Rplus' H w1) w3
.
*)

(*
Lemma Rplus_equals_Rplus' :
  forall H w, Rplus H w = Rplus' H w.
Proof.
  intros H w.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split;
  intros x Hx.
  - (* to show ⊆ *)
  (*
  inversion Hx as [p w' Hp x' Hwx EQw' EQx'
    | p w' w2 x' Hp Hw2 Hwx EQw' EQx'];
  clear w' EQw' x' EQx' Hx.
  *)
  induction Hx as [p w Hp x Hwx
    | p w w2 x Hp Hw2 IH Hwx].
  + (* when Rplus_base *)
  generalize dependent Hwx.
  now apply Rplus'_base.
  + (* when Rplus_trans *)
  generalize dependent w2.
  induction IH as [q w' Hq x' Hw'x'
    | q w' w2' x' Hq Hw'w2' Hw2'x' IH].
  *
  apply Rplus'_trans with (p:=q) (w2:=x');
  try assumption.
  generalize dependent Hwx.
  now apply Rplus'_base.
  *
  apply IHHw2.


  intros H p w1 w2 w3 Hp H12 H23.
  generalize dependent w3.
  induction H12 as [q w1 Hq w2 H12
    |q w1 w2 w3 Hq H12 H23 IH].
  - (* base case *)
  intros w3 H23.
  apply Rplus_trans with (p:=q) (w2:=w2);
  try assumption.
  generalize dependent w3.
  now apply Rplus_base.
  - (* inductive case *)
  intros w4 H34.
  apply Rplus_trans with (p:=q) (w2:=w2);
  try assumption.
  now apply IH.
Qed.
*)

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
  inversion Hx as [w' x' H'x EQw' EQx'];
  clear w' EQw' x' EQx' Hx.
  induction H'x as [w x Hx
    | w x y HRPx IH Hx];
  inversion Hx as [p' w' Hpp' x' H'x EQw' EQx'];
  clear w' EQw' x' EQx';
  inversion Hpp' as [EQp];
  rewrite <- EQp in H'x;
  rewrite <- EQp;
  clear p' Hpp' EQp.
  + (* when tc_il_base *)
  apply H'x.
  + (* when tc_il_trans *)
  destruct K_is_KD45 as [_ [Htra _]].
  unfold transitive in Htra.
  now apply Htra with (w':=x).

  - (* to show ⊇ *)
  assert (H'x : In _ (tcInitLast _ (Rh (Singleton _ p)) w) x).
  { apply tc_il_base. generalize dependent x. apply Rh_intro. apply In_singleton. }
  clear Hx.
  generalize dependent x.
  apply Rplus_intro.
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

Lemma B_p_positive_introspection :
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

Lemma B_p_negative_introspection :
  forall (p : P) (E : Ensemble W),
  Complement _ (B p E)
    = B p (Complement _ (B p E)).
Proof.
  destruct K_is_KD45 as [Hser [Htra Heuc]].

  intros p E.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split;
  unfold Included, Complement, In;
  intros x Hx.
  - (* to show ⊆ *)
  apply B_intro.
  unfold Included, In.
  intros y Hxy HBy.
  inversion HBy as [y' Hy EQy'];
  clear y' EQy' HBy.
  apply Hx.
  apply B_intro.
  unfold Included.
  intros z Hz.
  apply Hy.
  apply Heuc with (w:=x);
  [apply Hxy | apply Hz].

  - (* to show ⊇ *)
  destruct (Hser p x) as [x' Hxx'].

  inversion Hx as [w' HnB EQw'];
  clear w' EQw' Hx.
  unfold Included in HnB.
  specialize (HnB _ Hxx').
  unfold In in HnB.
  intros HBx;
  apply HnB.
  apply B_intro.
  unfold Included.
  intros y Hy.
  inversion HBx as [x'' HxE EQx''];
  clear x'' EQx'' HBx.
  apply HxE.
  now apply Htra with (w':=x').
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
  apply B_p_positive_introspection.
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

Definition Bh (H : Ensemble P) (E : Ensemble W) : Ensemble W :=
  IntersectionForall H (fun p => B p E).

Definition posnat (n : nat) : Prop := n > 0.

Lemma CB_H_equals_CB_H_pow_Bh_H :
  forall H E n,
  CB H E = CB H (fpow (Bh H) n E).
Proof.
  intros H E n.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.

  - (* to show ⊆ *)
  induction n as [| n IHn].
  + (* when n = 0 *)
  now unfold fpow.

  + (* when n > 0 *)
  intros x Hx.
  apply CB_intro.
  intros y Hxy.
  apply IHn in Hx as H'x.
  inversion H'x as [x' H''x EQx'];
  clear x' EQx' H'x.

  unfold fpow;
  fold (@fpow (Ensemble W)).
  apply IntersectionForall_intro.
  intros p Hp.
  apply B_intro.
  intros z Hyz.

  apply H''x.
  now apply Rplus_trans with (p:=p) (w2:=y).

  - (* to show ⊇ *)
  induction n as [| n IHn].
  + (* when n = 0 *)
  now unfold fpow.

  + (* when n > 0 *)
  intros x Hx.
  apply IHn.
  apply CB_intro.
  intros y Hxy.

  inversion Hx as [x' H'x EQx'];
  clear x' EQx' Hx.
  apply H'x in Hxy as H'xy.
  unfold fpow in H'xy;
  fold (@fpow (Ensemble W)) in H'xy.
  inversion H'xy as [x' H''xy EQx'];
  clear x' EQx' H'xy.

  inversion Hxy as [x' y' H'xy EQx' EQy'];
  clear x' EQx' y' EQy' Hxy.

  inversion H'xy as [x' y' HRh EQx' EQy'
    | x' w2 y' HRx2 HRh EQx' EQy'];
  clear x' EQx' y' EQy';
  inversion HRh as [p x' Hp y' HRxy EQx' EQy'];
  clear x' EQx' y' EQy' HRh;
  specialize (H''xy p Hp);
  inversion H''xy as [x' Hy EQx'];
  clear x' EQx';
  apply Hy;
  apply same_R_p in HRxy as EQRp;
  [| assumption | | assumption];
  now rewrite <- EQRp.
Qed.

Lemma CB_equals_intersection_of_Bh :
  forall H E,
  CB H E = IntersectionForall posnat
             (fun n => fpow (Bh H) n E).
Proof.
  intros H E.
  apply Extensionality_Ensembles.
  unfold Same_set.
  split;
  unfold Included;
  intros x Hx.
  - (* to show ⊆ *)
  apply IntersectionForall_intro.
  intros n Hn.
  unfold posnat, In in Hn.
  destruct n as [| m];
  [inversion Hn | clear Hn].
  induction m as [| m IHm].
  + (* when n = 1 *)
  unfold fpow.
  apply IntersectionForall_intro.
  intros p Hp.
  apply B_intro.
  intros y Hxy.
  inversion Hx as [w' HRPx EQw'];
  clear w' EQw' Hx.
  apply HRPx.
  generalize dependent y.
  now apply Rplus_base.
  + (* when n > 1 *)
  unfold fpow.
  unfold fpow in IHm.
  fold (@fpow (Ensemble W)).
  fold (@fpow (Ensemble W)) in IHm.

  rewrite CB_H_equals_CB_H_pow_Bh_H with (n:=S m) in Hx.
  inversion Hx as [w' HRPx EQw'];
  clear w' EQw' Hx.
  unfold fpow in HRPx;
  fold (@fpow (Ensemble W)) in HRPx.

  apply IntersectionForall_intro.
  intros p Hp.
  apply B_intro.
  intros y Hxy.
  apply HRPx.
  generalize dependent y.
  now apply Rplus_base.

  - (* to show ⊇ *)
  assert (Hpos : forall n, In _ posnat (S n)).
  { unfold posnat, In; apply Nat.lt_0_succ. }

  apply CB_intro.
  unfold Included.
  intros y Hy.
  inversion Hy as [x' y' H'y EQx' EQy'];
  clear x' EQx' y' EQy' Hy.
  rewrite <- tcHeadTail_equals_tcInitLast in H'y.
  induction H'y as [x y Hxy
    | x y z Hxy Hyz IH];
  inversion Hxy as [p x' Hp y' H'xy EQx' EQy'];
  clear x' EQx' y' EQy' Hxy.

  + (* when y ∈ Rh H x *)
  inversion Hx as [x' H'x EQx'];
  clear x' EQx' Hx.
  specialize (H'x 1 (Hpos 0)).
  inversion H'x as [x' Hx EQx'];
  clear x' EQx' H'x.

  specialize (Hx p Hp).
  inversion Hx as [x' H'x EQx'].
  now apply H'x.

  + (* when y ∈ Rh H x /\ z ∈ Rplus H y *)
  apply IH; clear IH.
  apply IntersectionForall_intro.
  intros n Hn.

  inversion Hx as [x' H'x EQx'];
  clear x' EQx' Hx.
  specialize (H'x (S n) (Hpos n)).
  inversion H'x as [x' Hx EQx'];
  clear x' EQx' H'x.

  specialize (Hx p Hp).
  inversion Hx as [x' H'x EQx'].
  now apply H'x.
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
