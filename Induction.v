From LF Require Export Basics.

(* Proof by Induction *)

Theorem add_0_r_firsttry :
  forall n : nat,
  n + 0 = n.
Proof.
  intros n.
  simpl.
Abort.

Theorem add_0_r_secondtry :
  forall n : nat,
  n + 0 = n.
Proof.
  intros n.
  destruct n as [|n'] eqn:E.
  - reflexivity.
  - simpl.
Abort.

Theorem add_0_r :
  forall n : nat,
  n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem minus_n_n :
  forall n,
  minus n n = 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem mul_0_r :
  forall n : nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm :
  forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem add_comm :
  forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - rewrite -> add_0_r with m.
    reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Theorem add_assoc :
  forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus :
  forall n,
  double n = n + n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Theorem eqb_refl:
  forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem even_S :
  forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n.
  simpl.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite negb_involutive.
    reflexivity.
Qed.

(* Proofs Within Proofs *)

Theorem mult_0_plus' :
  forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
  {
    rewrite add_comm.
    simpl.
    rewrite add_comm.
    reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry :
  forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite add_comm.
Abort.

Theorem plus_rearrange :
  forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  {
    rewrite add_comm.
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

(* Formal vs. Informal Proof *)

Theorem add_assoc' :
  forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn].
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem add_assoc'' :
  forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn].
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

(* More Exercises *)

Theorem add_shuffle3 :
  forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: n + m = m + n).
  {
    rewrite add_comm.
    reflexivity.
  }
  rewrite add_assoc, add_assoc.
  rewrite H.
  reflexivity.
Qed.

Lemma mul_n_Sm :
  forall n m : nat,
  n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [|n' IHn].
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    rewrite -> add_assoc, add_assoc.
    assert (H : m + n' = n' + m).
    {
      rewrite -> add_comm.
      reflexivity.
    }
    rewrite -> H.
    reflexivity.
Qed.

Theorem mul_comm :
  forall m n : nat,
  n * m = m * n.
Proof.
  intros n m.
  induction n as [|n' IHn].
  - rewrite mul_0_r.
    reflexivity.
  - simpl.
    rewrite mul_n_Sm.
    rewrite IHn.
    reflexivity.
Qed.

Check leb.

Lemma add_0_l :
  forall n : nat,
  0 + n = n.
Proof.
  intros.
  rewrite add_comm.
  rewrite add_0_r.
  reflexivity.
Qed.

Lemma plus_1_r :
  forall n : nat,
  n + 1 = S n.
Proof.
  intros.
  rewrite add_comm.
  rewrite plus_1_l.
  reflexivity.
Qed.

Lemma plus_Sn_Sm:
  forall m n : nat,
  S n + S m = S(S(n + m)).
Proof.
  intros.
  induction n.
  - rewrite add_0_l.
    rewrite plus_1_l.
    reflexivity.
  - simpl.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Lemma plus_Sn_m :
  forall m n : nat,
  (S n) + m = S(n + m).
Proof.
  intros n m.
  rewrite add_comm.
  induction n.
  - rewrite add_0_r.
    rewrite add_0_l.
    reflexivity.
  - rewrite plus_n_Sm.
    rewrite plus_Sn_Sm.
    rewrite <- plus_n_Sm, <- plus_n_Sm.
    rewrite add_comm.
    reflexivity.
Qed.

Theorem plus_leb_compat_l :
  forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p n_le_m.
  assert (H : (p + n) <=? (p + m) = true).
  {
    induction p.
    - rewrite add_0_l, add_0_l.
      rewrite n_le_m.
      reflexivity.
    - rewrite plus_Sn_m, plus_Sn_m.
      simpl.
      rewrite IHp.
      reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

Theorem leb_refl :
  forall n : nat,
  (n <=? n) = true.
Proof.
  intros.
  induction n.
  - reflexivity.
  - rewrite <- IHn.
    reflexivity.
Qed.

Theorem zero_neqb_S :
  forall n:nat,
  0 =? (S n) = false.
Proof.
  intros.
  induction n.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_false_r :
  forall b : bool,
  andb b false = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem S_neqb_0 :
  forall n:nat,
  (S n) =? 0 = false.
Proof.
  intros.
  induction n.
  - reflexivity.
  - reflexivity.
Qed.

Theorem mult_1_l :
  forall n:nat,
  1 * n = n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - rewrite mul_n_Sm.
    rewrite plus_1_l.
    rewrite IHn.
    reflexivity.
Qed.

Theorem all3_spec :
  forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma mul_0_l :
  forall n : nat,
  0 * n = 0.
Proof.
  intros.
  reflexivity.
Qed.

Theorem mult_plus_distr_r :
  forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite add_assoc.
    reflexivity.
Qed.

Theorem mult_assoc :
  forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite mult_plus_distr_r.
    reflexivity.
Qed.

Theorem add_shuffle3' :
  forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc, add_assoc.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite add_comm.
    reflexivity.
Qed.

(* Nat to Bin and Back to Nat *)

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 b' => B1 b'
  | B1 b' => B0 (incr b')
  end.

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => O
  | B0 b' => 2 * (bin_to_nat b')
  | B1 b' => 1 + 2 * (bin_to_nat b')
  end.

Theorem bin_to_nat_pres_incr :
  forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros.
  induction b.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite IHb.
    rewrite plus_1_l.
    rewrite <- plus_Sn_Sm.
    reflexivity.
Qed.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat :
  forall n,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite bin_to_nat_pres_incr.
    rewrite IHn.
    rewrite plus_1_l.
    reflexivity.
Qed.

(* Bin to Nat and Back to Bin (Advanced) *)

Theorem bin_nat_bin_fails :
  forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

Lemma double_incr :
  forall n : nat, double (S n) = S (S (double n)).
Proof.
  intros.
  rewrite double_plus.
  rewrite double_plus.
  rewrite plus_Sn_Sm.
  reflexivity.
Qed.

Definition double_bin (b:bin) : bin :=
  match b with
  | Z => Z
  | b' => B0 b'
  end.

Example double_bin_zero :
  double_bin Z = Z.
Proof.
  reflexivity.
Qed.

Lemma double_incr_bin :
  forall b,
  double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros.
  induction b.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint normalize (b : bin) : bin :=
  match b with
  | Z => Z
  | B0 b' => double_bin(normalize b')
  | B1 b' => incr (double_bin (normalize b'))
  end.

Example normalize_1:
  normalize Z = Z.
Proof.
  reflexivity.
Qed.

Example normalize_2:
  normalize (incr (B1 (B0 (B1 (B0 Z))))) = (B0 (B1 (B1 Z))).
Proof.
  reflexivity.
Qed.

Example normalize_3:
  Z = normalize (B0 Z).
Proof.
  reflexivity.
Qed.

Example normalize_4:
  B1 Z = normalize (B1 Z).
Proof.
  reflexivity.
Qed.

Example normalize_5:
  B0 (B1 Z) = normalize (B0 (B1 Z)).
Proof.
  reflexivity.
Qed.

Lemma normalize_double_bin :
  forall b : bin,
  normalize (double_bin b) = double_bin (normalize b).
Proof.
  intros.
  induction b.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma normalize_incr_double_bin :
  forall b : bin,
  normalize (incr (double_bin b)) = incr (double_bin (normalize b)).
Proof.
  intros.
  induction b.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem normalize_incr :
  forall b : bin,
  incr (normalize b) = normalize (incr b).
Proof.
  intros.
  induction b.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite <- IHb.
    rewrite <- double_incr_bin.
    reflexivity.
Qed.

Compute normalize (double_bin (B0 Z)).
Compute double_bin (normalize (B0 Z)).

Theorem normalize_idemp :
  forall b: bin,
  normalize b = normalize (normalize b).
Proof.
  intro.
  induction b.
  - reflexivity.
  - simpl.
    rewrite normalize_double_bin.
    rewrite <- IHb.
    reflexivity.
  - simpl.
    rewrite normalize_incr_double_bin.
    rewrite <- IHb.
    reflexivity.
Qed.

Lemma double_incur_nat_to_bin :
  forall n : nat,
  nat_to_bin (n + n + 1) = incr (double_bin (nat_to_bin n)).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    replace (n + S n) with (S (n + n)).
    + simpl.
      rewrite double_incr_bin.
      rewrite IHn.
      reflexivity.
    + rewrite plus_n_Sm.
      reflexivity.
Qed.

Lemma double_nat_to_bin :
  forall n : nat,
  nat_to_bin (n + n) = double_bin (nat_to_bin n).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    replace (n + S n) with (S (n + n)).
    + simpl.
      rewrite double_incr_bin.
      rewrite IHn.
      reflexivity.
    + rewrite plus_n_Sm.
      reflexivity.
Qed.

Theorem bin_nat_bin :
  forall b: bin, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros.
  induction b.
  - reflexivity.
  - simpl.
    rewrite add_0_r.
    rewrite double_nat_to_bin.
    rewrite IHb.
    reflexivity.
  - simpl.
    rewrite add_0_r.
    rewrite double_nat_to_bin.
    rewrite IHb.
    reflexivity.
Qed.
