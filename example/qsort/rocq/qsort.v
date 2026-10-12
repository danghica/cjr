(** In-place quicksort over an abstract length/get/set array.

The same algorithm is instantiated for the fixed array and for the array list.
Neither instance unfolds the representation: each one supplies the three
library specifications. The functional [qsort] is what the imperative code
computes. It is a sorted permutation of its input. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws.
From cjr.examples Require Import array array_list.
From iris.prelude Require Import options.
From Coq Require Import Lia.
Close Scope expr_scope.

(** * The functional algorithm

Lomuto partition on a half-open slice. The pivot is the last element. The
scan swaps a value into the stored prefix when it is [≤] the pivot, then
places the pivot at the boundary. [qsort_slice] sorts [lo, hi) and leaves
every other index alone. *)

Definition swap_list (xs : list Z) (i j : nat) : list Z :=
  match xs !! i, xs !! j with
  | Some xi, Some xj => <[i := xj]> (<[j := xi]> xs)
  | _, _ => xs
  end.

Fixpoint lomuto (n : nat) (xs : list Z) (pivot : Z) (i j bound : nat)
  : list Z * nat :=
  match n with
  | O => (xs, i)
  | S n =>
      if Nat.ltb j bound then
        match xs !! j with
        | Some v =>
            if Z.leb v pivot then
              lomuto n (swap_list xs i j) pivot (S i) (S j) bound
            else lomuto n xs pivot i (S j) bound
        | None => (xs, i)
        end
      else (xs, i)
  end.

Definition partition_list (xs : list Z) (lo hi : nat) : list Z * nat :=
  match xs !! (hi - 1)%nat with
  | Some pivot =>
      match lomuto ((hi - 1) - lo)%nat xs pivot lo lo (hi - 1)%nat with
      | (zs, q) => (swap_list zs q (hi - 1)%nat, q)
      end
  | None => (xs, lo)
  end.

Fixpoint qsort_slice (n : nat) (xs : list Z) (lo hi : nat) : list Z :=
  match n with
  | O => xs
  | S n =>
      if Nat.leb hi (lo + 1)%nat then xs
      else
        let '(ys, p) := partition_list xs lo hi in
        qsort_slice n (qsort_slice n ys lo p) (S p) hi
  end.

Definition qsort (xs : list Z) : list Z :=
  qsort_slice (length xs) xs 0%nat (length xs).

Definition slice_sorted (xs : list Z) (lo hi : nat) : Prop :=
  ∀ i j x y, (lo ≤ i)%nat → (i < j)%nat → (j < hi)%nat →
    xs !! i = Some x → xs !! j = Some y → (x ≤ y)%Z.

(** * List facts used by the partition invariant *)

Lemma swap_list_length xs i j :
  length (swap_list xs i j) = length xs.
Proof.
  rewrite /swap_list.
  destruct (xs !! i) as [xi|]; [|done].
  destruct (xs !! j) as [xj|]; [|done].
  by rewrite !length_insert.
Qed.

Lemma swap_list_id xs i x :
  xs !! i = Some x → swap_list xs i i = xs.
Proof.
  intros Hi. rewrite /swap_list Hi.
  rewrite list_insert_insert list_insert_id; done.
Qed.

Lemma swap_lookup xs i j xi xj k :
  xs !! i = Some xi → xs !! j = Some xj →
  swap_list xs i j !! k =
    if decide (k = i) then Some xj
    else if decide (k = j) then Some xi else xs !! k.
Proof.
  intros Hi Hj. rewrite /swap_list Hi Hj.
  destruct (decide (k = i)) as [->|Hki].
  - rewrite list_lookup_insert; [done|].
    rewrite length_insert. by eapply lookup_lt_Some.
  - destruct (decide (k = j)) as [->|Hkj].
    + rewrite list_lookup_insert_ne; last done.
      rewrite list_lookup_insert; [done|].
      by eapply lookup_lt_Some.
    + rewrite list_lookup_insert_ne; last done.
      by rewrite list_lookup_insert_ne.
Qed.

Lemma move_cons (xs ys : list Z) (a : Z) :
  xs ++ a :: ys ≡ₚ a :: xs ++ ys.
Proof.
  induction xs as [|x xs IH]; [done|].
  simpl. rewrite IH. apply Permutation_swap.
Qed.

Lemma exchange (pre mid suf : list Z) (x y : Z) :
  pre ++ x :: mid ++ y :: suf ≡ₚ pre ++ y :: mid ++ x :: suf.
Proof.
  apply Permutation_app_head.
  assert ((x :: mid) ++ y :: suf ≡ₚ y :: (x :: mid) ++ suf) as H1
    by apply move_cons.
  simpl in H1. rewrite H1.
  apply Permutation_skip. symmetry. apply (move_cons mid suf x).
Qed.

Lemma count_insert xs i y x z :
  xs !! i = Some y →
  count_occ Z.eq_dec (<[i:=x]> xs) z + (if Z.eq_dec z y then 1 else 0)
    = count_occ Z.eq_dec xs z + (if Z.eq_dec z x then 1 else 0).
Proof.
  revert i. induction xs as [|h xs IH]; intros [|i] Hi; simplify_eq/=.
  - destruct (Z.eq_dec z y), (Z.eq_dec z x), (Z.eq_dec y z), (Z.eq_dec x z);
      simpl; lia.
  - destruct (Z.eq_dec h z), (Z.eq_dec z h); simpl;
      rewrite (IH i Hi); reflexivity.
Qed.

Lemma swap_list_perm xs i j xi xj :
  xs !! i = Some xi → xs !! j = Some xj →
  swap_list xs i j ≡ₚ xs.
Proof.
  intros Hi Hj.
  destruct (decide (i = j)) as [->|Hij].
  { rewrite (swap_list_id xs j xi); done. }
  apply (Permutation_count_occ Z.eq_dec). intros z.
  rewrite /swap_list Hi Hj.
  assert (xs !! i = Some xi) as Hi' by done.
  assert ((<[j:=xi]> xs) !! i = Some xi) as Hi1.
  { rewrite list_lookup_insert_ne; done. }
  pose proof (count_insert xs j xj xi z Hj) as Hc1.
  pose proof (count_insert (<[j:=xi]> xs) i xi xj z Hi1) as Hc2.
  lia.
Qed.

Lemma take_lookup_eq (xs ys : list Z) n :
  (n ≤ length xs)%nat → (n ≤ length ys)%nat →
  (∀ k, (k < n)%nat → xs !! k = ys !! k) →
  take n xs = take n ys.
Proof.
  revert xs ys. induction n as [|n IH]; intros xs ys Hx Hy Hk.
  - by rewrite !take_0.
  - destruct xs as [|x xs]; [simpl in Hx; lia|].
    destruct ys as [|y ys]; [simpl in Hy; lia|].
    simpl.
    assert ((0 < S n)%nat) as H0 by lia.
    pose proof (Hk 0%nat H0) as Hhead. simpl in Hhead. simplify_eq.
    simpl in Hx, Hy. apply le_S_n in Hx. apply le_S_n in Hy.
    f_equal. apply IH; [exact Hx|exact Hy|].
    intros k Hk'.
    assert ((S k < S n)%nat) as HSk by lia.
    pose proof (Hk (S k) HSk) as Htail. simpl in Htail. exact Htail.
Qed.

Lemma drop_lookup_eq (xs ys : list Z) n :
  length xs = length ys →
  (∀ k, (n ≤ k)%nat → xs !! k = ys !! k) →
  drop n xs = drop n ys.
Proof.
  revert xs ys n. induction xs as [|x xs IH]; intros ys n Hlen Hk.
  - destruct ys; [|simpl in Hlen; lia]. by rewrite drop_nil.
  - destruct ys as [|y ys]; [simpl in Hlen; lia|].
    simpl in Hlen. apply Nat.succ_inj in Hlen.
    destruct n as [|n].
    + pose proof (Hk 0%nat (le_n 0)) as H0. simpl in H0. simplify_eq.
      simpl. f_equal. apply (IH ys 0%nat Hlen).
      intros k Hk'.
      pose proof (Hk (S k) (Nat.le_0_l (S k))) as Ht. simpl in Ht. exact Ht.
    + apply (IH ys n Hlen).
      intros k Hk'.
      pose proof (Hk (S k) (le_n_S _ _ Hk')) as Ht.
      simpl in Ht. exact Ht.
Qed.

Fixpoint count_if (P : Z → bool) (xs : list Z) : nat :=
  match xs with
  | [] => 0
  | x :: xs => (if P x then 1%nat else 0%nat) + count_if P xs
  end.

Lemma count_if_app P xs ys :
  count_if P (xs ++ ys) = (count_if P xs + count_if P ys)%nat.
Proof. induction xs; simpl; lia. Qed.

Lemma count_if_perm P xs ys : xs ≡ₚ ys → count_if P xs = count_if P ys.
Proof.
  induction 1; simpl; lia.
Qed.

Lemma count_if_take_drop P xs n :
  count_if P xs = (count_if P (take n xs) + count_if P (drop n xs))%nat.
Proof. rewrite <- count_if_app, take_drop. done. Qed.

Lemma region_count P xs lo hi :
  (lo ≤ hi)%nat → (hi ≤ length xs)%nat →
  count_if P xs =
    (count_if P (take lo xs) +
     count_if P (take (hi - lo) (drop lo xs)) +
     count_if P (drop hi xs))%nat.
Proof.
  intros Hlo Hhi.
  rewrite (count_if_take_drop _ _ lo).
  rewrite (count_if_take_drop _ (drop lo xs) (hi - lo)).
  rewrite drop_drop. rewrite Nat.add_assoc.
  do 2 f_equal. by replace (lo + (hi - lo))%nat with hi by lia.
Qed.

Lemma take_region_zero P xs lo hi :
  (lo ≤ hi ≤ length xs)%nat →
  (∀ k x, (lo ≤ k < hi)%nat → xs !! k = Some x → P x = false) →
  count_if P (take (hi - lo) (drop lo xs)) = 0%nat.
Proof.
  intros Hbound Hall.
  remember (hi - lo)%nat as n eqn:Hn. revert lo hi Hn Hbound Hall.
  induction n as [|n IH]; intros lo hi Hn Hbound Hall; [by rewrite take_0|].
  destruct (lookup_lt_is_Some_2 xs lo) as [x Hx].
  { lia. }
  rewrite (drop_S xs x lo Hx).
  replace (hi - lo)%nat with (S (hi - S lo)) by lia.
  simpl. rewrite (Hall lo x); [|lia|exact Hx].
  simpl. apply (IH (S lo) hi).
  - lia.
  - lia.
  - intros k y Hk Hy. apply (Hall k y); [lia|exact Hy].
Qed.

Lemma count_zero_lookup P xs lo hi k x :
  (lo ≤ hi ≤ length xs)%nat →
  count_if P (take (hi - lo) (drop lo xs)) = 0%nat →
  (lo ≤ k < hi)%nat → xs !! k = Some x → P x = false.
Proof.
  intros Hbound Hcount Hk Hx.
  remember (hi - lo)%nat as n eqn:Hn.
  revert lo hi k Hn Hbound Hk Hx Hcount.
  induction n as [|n IH]; intros lo hi k Hn Hbound Hk Hx Hcount.
  { lia. }
  destruct (lookup_lt_is_Some_2 xs lo) as [y Hy].
  { lia. }
  rewrite (drop_S xs y lo Hy) in Hcount.
  replace (hi - lo)%nat with (S (hi - S lo)) in Hcount by lia.
  simpl in Hcount.
  destruct (decide (k = lo)) as [->|Hne].
  -     rewrite Hx in Hy. injection Hy as Heq. subst x.
    destruct (P y); simpl in Hcount; lia.
  - destruct (P y); simpl in Hcount; [lia|].
    apply (IH (S lo) hi k); [lia|lia|lia|done|done].
Qed.

Lemma region_preserved (P : Z → bool) (xs ys : list Z) (lo hi : nat) :
  length ys = length xs →
  (lo ≤ hi ≤ length xs)%nat →
  (∀ k, (k < lo ∨ hi ≤ k)%nat → ys !! k = xs !! k) →
  ys ≡ₚ xs →
  (∀ k x, (lo ≤ k < hi)%nat → xs !! k = Some x → P x = true) →
  ∀ k x, (lo ≤ k < hi)%nat → ys !! k = Some x → P x = true.
Proof.
  intros Hlen Hbound Hout Hperm Hall k x Hk Hx.
  pose (Q := λ z, negb (P z)).
  assert (count_if Q (take (hi - lo) (drop lo xs)) = 0%nat) as Hzero.
  { apply take_region_zero; [lia|]. intros m y Hm Hy.
    unfold Q. by rewrite (Hall m y Hm Hy). }
  assert (take lo ys = take lo xs) as Htake.
  { apply take_lookup_eq; [lia|lia|].
    intros m Hm. rewrite <- (Hout m); [done|lia]. }
  assert (drop hi ys = drop hi xs) as Hdrop.
  { apply drop_lookup_eq; [lia|].
    intros m Hm. rewrite <- (Hout m); [done|lia]. }
  assert (count_if Q ys = count_if Q xs) as Hcount by by apply count_if_perm.
  rewrite (region_count Q ys lo hi) in Hcount; [|lia|lia].
  rewrite (region_count Q xs lo hi) in Hcount; [|lia|lia].
  rewrite Htake Hdrop in Hcount.
  assert (count_if Q (take (hi - lo) (drop lo ys)) = 0%nat) as Hzero'.
  { lia. }
  assert (Q x = false) as Hq.
  { apply (count_zero_lookup Q ys lo hi k x); [lia|exact Hzero'|exact Hk|exact Hx]. }
  unfold Q in Hq. destruct (P x); simpl in Hq; done.
Qed.

(** * Partition and sorting *)

Record lomuto_inv (xs0 xs : list Z) (lo i j bound : nat) (pivot : Z) : Prop := {
  linv_len : length xs = length xs0;
  linv_perm : xs ≡ₚ xs0;
  linv_lo : (lo ≤ i)%nat;
  linv_ij : (i ≤ j)%nat;
  linv_jb : (j ≤ bound)%nat;
  linv_lenb : (bound < length xs)%nat;
  linv_piv : xs !! bound = Some pivot;
  linv_out : ∀ k, (k < lo ∨ bound < k)%nat → xs !! k = xs0 !! k;
  linv_left : ∀ k x, (lo ≤ k < i)%nat → xs !! k = Some x → (x ≤ pivot)%Z;
  linv_mid : ∀ k x, (i ≤ k < j)%nat → xs !! k = Some x → (pivot < x)%Z
}.

Lemma lomuto_step xs0 xs lo i j bound pivot v :
  lomuto_inv xs0 xs lo i j bound pivot →
  (j < bound)%nat →
  xs !! j = Some v →
  lomuto_inv xs0
    (if Z.leb v pivot then swap_list xs i j else xs)
    lo (if Z.leb v pivot then S i else i) (S j) bound pivot.
Proof.
  intros Hinv Hjb Hv.
  pose proof (linv_lo _ _ _ _ _ _ _ Hinv) as Hlo.
  pose proof (linv_ij _ _ _ _ _ _ _ Hinv) as Hij.
  pose proof (linv_jb _ _ _ _ _ _ _ Hinv) as Hjbound.
  pose proof (linv_lenb _ _ _ _ _ _ _ Hinv) as Hlenb.
  destruct (Z.leb v pivot) eqn:Hleb.
  - apply Z.leb_le in Hleb.
    destruct (lookup_lt_is_Some_2 xs i) as [xi Hxi]; [lia|].
    split.
    + rewrite swap_list_length. apply (linv_len _ _ _ _ _ _ _ Hinv).
    + etrans; [|apply (linv_perm _ _ _ _ _ _ _ Hinv)].
      apply (swap_list_perm xs i j xi v); done.
    + lia.
    + lia.
    + lia.
    + rewrite swap_list_length. apply (linv_lenb _ _ _ _ _ _ _ Hinv).
    + rewrite (swap_lookup xs i j xi v bound); [|done|done].
      destruct (decide (bound = i)) as [->|Hi]; [lia|].
      destruct (decide (bound = j)) as [->|Hj]; [lia|].
      apply (linv_piv _ _ _ _ _ _ _ Hinv).
    + intros k Hk.
      rewrite (swap_lookup xs i j xi v k); [|done|done].
      destruct (decide (k = i)) as [->|Hki]; [lia|].
      destruct (decide (k = j)) as [->|Hkj]; [lia|].
      apply (linv_out _ _ _ _ _ _ _ Hinv). lia.
    + intros k x Hk Hx.
      rewrite (swap_lookup xs i j xi v k) in Hx; [|done|done].
      destruct (decide (k = i)) as [->|Hki].
      * simplify_eq. done.
      * destruct (decide (k = j)) as [->|Hkj]; [lia|].
        apply (linv_left _ _ _ _ _ _ _ Hinv k x); [lia|done].
    + intros k x Hk Hx.
      destruct (decide (i = j)) as [->|Hneq]; [lia|].
      assert ((i < j)%nat) as Hltij by lia.
      rewrite (swap_lookup xs i j xi v k) in Hx; [|done|done].
      destruct (decide (k = i)) as [->|Hki]; [lia|].
      destruct (decide (k = j)) as [->|Hkj].
      * assert (x = xi) as -> by congruence.
        apply (linv_mid _ _ _ _ _ _ _ Hinv i xi); [lia|exact Hxi].
      * apply (linv_mid _ _ _ _ _ _ _ Hinv k x); [lia|done].
  - assert ((pivot < v)%Z) as Hgt.
    { apply Z.leb_gt. exact Hleb. }
    split.
    + apply (linv_len _ _ _ _ _ _ _ Hinv).
    + apply (linv_perm _ _ _ _ _ _ _ Hinv).
    + apply (linv_lo _ _ _ _ _ _ _ Hinv).
    + lia.
    + lia.
    + apply (linv_lenb _ _ _ _ _ _ _ Hinv).
    + apply (linv_piv _ _ _ _ _ _ _ Hinv).
    + intros k Hk. apply (linv_out _ _ _ _ _ _ _ Hinv). lia.
    + intros k x Hk Hx. apply (linv_left _ _ _ _ _ _ _ Hinv k x); [lia|done].
    + intros k x Hk Hx.
      destruct (decide (k = j)) as [->|Hkj].
      * rewrite Hv in Hx. simplify_eq. done.
      * apply (linv_mid _ _ _ _ _ _ _ Hinv k x); [lia|done].
Qed.

Lemma lomuto_inv_start xs lo bound pivot :
  (lo ≤ bound)%nat →
  (bound < length xs)%nat →
  xs !! bound = Some pivot →
  lomuto_inv xs xs lo lo lo bound pivot.
Proof.
  intros Hlo Hlen Hpivot. unshelve econstructor.
  - done.
  - apply Permutation_refl.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact Hpivot.
  - intros k Hk. done.
  - intros k x Hk. lia.
  - intros k x Hk. lia.
Qed.

Lemma lomuto_go n xs0 xs lo i j bound pivot ys p :
  lomuto_inv xs0 xs lo i j bound pivot →
  (n = bound - j)%nat →
  lomuto n xs pivot i j bound = (ys, p) →
  lomuto_inv xs0 ys lo p bound bound pivot.
Proof.
  revert xs i j ys p. induction n as [|n IH]; intros xs i j ys p Hinv Hn Heq.
  - pose proof (linv_jb _ _ _ _ _ _ _ Hinv) as Hjb.
    assert (j = bound) as -> by lia. simpl in Heq. simplify_eq. exact Hinv.
  - simpl in Heq.
    assert (j < bound)%nat as Hjb by lia.
    rewrite (proj2 (Nat.ltb_lt j bound) Hjb) in Heq.
    pose proof (linv_lenb _ _ _ _ _ _ _ Hinv) as Hlenb.
    destruct (lookup_lt_is_Some_2 xs j) as [v Hv]; [lia|].
    rewrite Hv in Heq.
    destruct (Z.leb v pivot) eqn:Hleb.
    + apply (IH (swap_list xs i j) (S i) (S j) ys p) in Heq.
      * exact Heq.
      * pose proof (lomuto_step xs0 xs lo i j bound pivot v Hinv Hjb Hv) as Hstep.
        rewrite Hleb in Hstep. simpl in Hstep. exact Hstep.
      * lia.
    + apply (IH xs i (S j) ys p) in Heq.
      * exact Heq.
      * pose proof (lomuto_step xs0 xs lo i j bound pivot v Hinv Hjb Hv) as Hstep.
        rewrite Hleb in Hstep. simpl in Hstep. exact Hstep.
      * lia.
Qed.

Lemma slice_sorted_short xs lo hi :
  (hi ≤ lo + 1)%nat → slice_sorted xs lo hi.
Proof. intros ? i j ????. lia. Qed.

Lemma slice_sorted_join xs lo p hi pivot :
  (lo ≤ p)%nat → (p < hi)%nat →
  xs !! p = Some pivot →
  (∀ k x, (lo ≤ k < p)%nat → xs !! k = Some x → (x ≤ pivot)%Z) →
  (∀ k x, (p < k < hi)%nat → xs !! k = Some x → (pivot < x)%Z) →
  slice_sorted xs lo p →
  slice_sorted xs (S p) hi →
  slice_sorted xs lo hi.
Proof.
  intros Hlo Hp Hpivot Hleft Hright Hsl Hsr i j x y Hi Hij Hj Hx Hy.
  destruct (decide (j < p)) as [Hjp|Hjp].
  - apply (Hsl i j x y); [lia|lia|lia|done|done].
  - destruct (decide (i < p)) as [Hip|Hip].
    + destruct (decide (j = p)) as [->|Hne].
      * rewrite Hpivot in Hy. injection Hy as Heq. subst y.
        apply (Hleft i x); [lia|done].
      * assert ((pivot < y)%Z) as Hpy by (apply (Hright j y); [lia|done]).
        assert ((x ≤ pivot)%Z) as Hxp by (apply (Hleft i x); [lia|done]).
        lia.
    + destruct (decide (i = p)) as [->|Hie].
      * rewrite Hpivot in Hx. injection Hx as Heq. subst x.
        assert ((pivot < y)%Z) as Hpy by (apply (Hright j y); [lia|done]). lia.
      * apply (Hsr i j x y); [lia|lia|lia|done|done].
Qed.

Definition part_ok (xs ys : list Z) (lo hi p : nat) (pivot : Z) : Prop :=
  length ys = length xs ∧ ys ≡ₚ xs ∧ (lo ≤ p < hi)%nat ∧
  ys !! p = Some pivot ∧
  (∀ k, (k < lo ∨ hi ≤ k)%nat → ys !! k = xs !! k) ∧
  (∀ k x, (lo ≤ k < p)%nat → ys !! k = Some x → (x ≤ pivot)%Z) ∧
  (∀ k x, (p < k < hi)%nat → ys !! k = Some x → (pivot < x)%Z).

Lemma partition_list_ok xs lo hi ys p :
  (lo < hi)%nat → (hi ≤ length xs)%nat →
  partition_list xs lo hi = (ys, p) →
  ∃ pivot, part_ok xs ys lo hi p pivot.
Proof.
  intros Hlo Hhi Heq. rewrite /partition_list in Heq.
  set (bound := (hi - 1)%nat) in *.
  destruct (lookup_lt_is_Some_2 xs bound) as [pivot Hpivot]; [lia|].
  rewrite Hpivot in Heq.
  destruct (lomuto (bound - lo)%nat xs pivot lo lo bound) as [zs q] eqn:Hgo.
  simpl in Heq. simplify_eq.
  assert (lomuto_inv xs xs lo lo lo bound pivot) as Hinit.
  { unshelve econstructor.
    - done.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hpivot.
    - intros k Hk. done.
    - intros k x Hk Hx. lia.
    - intros k x Hk Hx. lia. }
  eapply lomuto_go in Hgo; [|exact Hinit|lia].
  pose proof (linv_lo _ _ _ _ _ _ _ Hgo) as Hplo.
  pose proof (linv_ij _ _ _ _ _ _ _ Hgo) as Hpbd.
  pose proof (linv_lenb _ _ _ _ _ _ _ Hgo) as Hblen.
  pose proof (linv_piv _ _ _ _ _ _ _ Hgo) as Hpiv.
  destruct (lookup_lt_is_Some_2 zs p) as [zq Hq]; [lia|].
  exists pivot. repeat split.
  - rewrite swap_list_length. apply (linv_len _ _ _ _ _ _ _ Hgo).
  - etrans; [|apply (linv_perm _ _ _ _ _ _ _ Hgo)].
    apply (swap_list_perm zs p bound zq pivot); [exact Hq|exact Hpiv].
  - lia.
  - lia.
  - rewrite (swap_lookup zs p bound zq pivot p); [|exact Hq|exact Hpiv].
    destruct (decide (p = p)) as [_|?]; [done|lia].
  - intros k Hk.
    rewrite (swap_lookup zs p bound zq pivot k); [|exact Hq|exact Hpiv].
    destruct (decide (k = p)) as [->|?]; [lia|].
    destruct (decide (k = bound)) as [->|?]; [lia|].
    apply (linv_out _ _ _ _ _ _ _ Hgo). lia.
  - intros k x Hk Hx.
    rewrite (swap_lookup zs p bound zq pivot k) in Hx; [|exact Hq|exact Hpiv].
    destruct (decide (k = p)) as [->|?]; [lia|].
    destruct (decide (k = bound)) as [->|?]; [lia|].
    apply (linv_left _ _ _ _ _ _ _ Hgo k x); [lia|exact Hx].
  - intros k x Hk Hx.
    rewrite (swap_lookup zs p bound zq pivot k) in Hx; [|exact Hq|exact Hpiv].
    destruct (decide (k = p)) as [->|?]; [lia|].
    destruct (decide (k = bound)) as [->|?].
    + injection Hx as <-.
      apply (linv_mid _ _ _ _ _ _ _ Hgo p zq); [lia|exact Hq].
    + apply (linv_mid _ _ _ _ _ _ _ Hgo k x); [lia|exact Hx].
Qed.

Lemma slice_sorted_same xs ys lo hi :
  (∀ k, (lo ≤ k < hi)%nat → ys !! k = xs !! k) →
  slice_sorted xs lo hi → slice_sorted ys lo hi.
Proof.
  intros Heq Hsorted i j x y Hi Hij Hj Hx Hy.
  apply (Hsorted i j x y); [exact Hi|exact Hij|exact Hj| |].
  - rewrite <- (Heq i); [|lia]. exact Hx.
  - rewrite <- (Heq j); [|lia]. exact Hy.
Qed.

Lemma qsort_slice_spec n xs lo hi :
  (hi ≤ length xs)%nat →
  (hi - lo ≤ n)%nat →
  let ys := qsort_slice n xs lo hi in
  length ys = length xs ∧ ys ≡ₚ xs ∧
  (∀ k, (k < lo ∨ hi ≤ k)%nat → ys !! k = xs !! k) ∧
  slice_sorted ys lo hi.
Proof.
  revert xs lo hi. induction n as [|n IH]; intros xs lo hi Hlen Hfuel.
  - assert (hi ≤ lo)%nat as Hempty by lia. simpl.
    split; [done|]. split; [apply Permutation_refl|]. split.
    + intros k Hk. done.
    + apply slice_sorted_short. lia.
  - simpl. destruct (Nat.leb hi (lo + 1)%nat) eqn:Hshort.
    + assert (hi ≤ lo + 1)%nat as Hle.
      { apply (proj1 (Nat.leb_le _ _)). exact Hshort. }
      simpl.
      split; [done|]. split; [apply Permutation_refl|]. split.
      * intros k Hk. done.
      * apply slice_sorted_short. exact Hle.
    + assert ((lo + 1 < hi)%nat) as Hlong.
      { apply Nat.lt_nge. intro Hle.
        rewrite (proj2 (Nat.leb_le _ _) Hle) in Hshort. discriminate. }
      destruct (partition_list xs lo hi) as [zs p] eqn:Hpart. simpl.
      assert (lo < hi)%nat as Hlt by lia.
      destruct (partition_list_ok xs lo hi zs p Hlt Hlen Hpart) as [pivot Hok].
      destruct Hok as [Hlenz [Hpermz [Hrange [Hpivot [Hout [Hleft Hright]]]]]].
      destruct Hrange as [Hplo Hp].
      assert (p ≤ length zs)%nat as Hlenp by (rewrite Hlenz; lia).
      assert (p - lo ≤ n)%nat as Hfuelp by lia.
      pose proof (IH zs lo p Hlenp Hfuelp) as H1.
      destruct H1 as [Hlen1 [Hperm1 [Hout1 Hsort1]]].
      set (ys1 := qsort_slice n zs lo p) in *.
      assert (hi ≤ length ys1)%nat as Hleny by (rewrite Hlen1 Hlenz; exact Hlen).
      assert (hi - S p ≤ n)%nat as Hfuely by lia.
      pose proof (IH ys1 (S p) hi Hleny Hfuely) as H2.
      destruct H2 as [Hlen2 [Hperm2 [Hout2 Hsort2]]].
      set (ys2 := qsort_slice n ys1 (S p) hi) in *.
      assert (∀ k x, (lo ≤ k < p)%nat → ys1 !! k = Some x → (x ≤ pivot)%Z) as Hleft1.
      { intros k x Hk Hx.
        assert (Z.leb x pivot = true) as Hleb.
        { eapply (region_preserved (λ z, Z.leb z pivot) zs ys1 lo p);
            [exact Hlen1|lia| | | |exact Hk|exact Hx].
          - intros m Hm. apply Hout1. lia.
          - exact Hperm1.
          - intros m y Hm Hy. apply Z.leb_le. apply (Hleft m y); [exact Hm|exact Hy]. }
        apply Z.leb_le. exact Hleb. }
      assert (∀ k x, (S p ≤ k < hi)%nat → ys1 !! k = Some x → (pivot < x)%Z) as Hright1.
      { intros k x Hk Hx.
        rewrite (Hout1 k) in Hx; [|lia].
        apply (Hright k x); [lia|exact Hx]. }
      repeat split.
      * rewrite Hlen2 Hlen1 Hlenz. done.
      * etrans; [exact Hperm2|]. etrans; [exact Hperm1|]. exact Hpermz.
      * intros k Hk.
        rewrite (Hout2 k); [|lia].
        rewrite (Hout1 k); [|lia].
        apply Hout. exact Hk.
      * apply (slice_sorted_join ys2 lo p hi pivot); [lia|lia| | | | |exact Hsort2].
        -- rewrite (Hout2 p); [|lia]. rewrite (Hout1 p); [|lia]. exact Hpivot.
        -- intros k x Hk Hx.
           rewrite (Hout2 k) in Hx; [|lia].
           apply (Hleft1 k x); [exact Hk|exact Hx].
        -- intros k x Hk Hx.
           assert (Z.ltb pivot x = true) as Hltb.
           { eapply (region_preserved (λ z, Z.ltb pivot z) ys1 ys2 (S p) hi);
               [rewrite Hlen2; done|lia| | | |exact Hk|exact Hx].
             - intros m Hm. apply Hout2. lia.
             - exact Hperm2.
             - intros m y Hm Hy. apply Z.ltb_lt. apply (Hright1 m y); [exact Hm|exact Hy]. }
           apply Z.ltb_lt. exact Hltb.
        -- apply slice_sorted_same with ys1; [|exact Hsort1].
           intros k Hk. apply Hout2. lia.
Qed.

Lemma qsort_perm xs : qsort xs ≡ₚ xs.
Proof.
  unfold qsort.
  destruct (qsort_slice_spec (length xs) xs 0%nat (length xs)) as [_ [Hperm _]];
    [lia|lia|exact Hperm].
Qed.

Lemma qsort_sorted xs : slice_sorted (qsort xs) 0%nat (length xs).
Proof.
  unfold qsort.
  destruct (qsort_slice_spec (length xs) xs 0%nat (length xs)) as [_ [_ [_ Hsorted]]];
    [lia|lia|exact Hsorted].
Qed.

Lemma qsort_example : qsort [3%Z; 1%Z; 2%Z] = [1%Z; 2%Z; 3%Z].
Proof. vm_compute. reflexivity. Qed.

Lemma swap_list_code xs i j xi xj :
  xs !! i = Some xi → xs !! j = Some xj →
  <[j := xi]> (<[i := xj]> xs) = swap_list xs i j.
Proof.
  intros Hi Hj. rewrite /swap_list Hi Hj.
  destruct (decide (i = j)) as [->|Hne].
  - assert (xi = xj) as -> by congruence.
    rewrite !list_insert_insert !list_insert_id; done.
  - rewrite (list_insert_commute _ j i xi xj); done.
Qed.

(** * One algorithm, two arrays

[get], [set], and [length] are parameters. [swap], [partition], and [qsort]
are built from them once. Each instance only has to supply the three
specifications. *)

Section qsort_alg.
  Set Default Proof Using "All".
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  Variable G : Type.
  Variable R : G → list Z → val → iProp Σ.
  Variable len_body get_body set_body : expr.

  Hypothesis len_sub : ∀ x v, x ≠ "a" → subst x v len_body = len_body.
  Hypothesis len_subvar : ∀ x (l : loc), x ≠ "a" → subst_var x l len_body = len_body.
  Hypothesis get_sub : ∀ x v, x ≠ "args" → subst x v get_body = get_body.
  Hypothesis get_subvar : ∀ x (l : loc), x ≠ "args" → subst_var x l get_body = get_body.
  Hypothesis set_sub : ∀ x v, x ≠ "args" → subst x v set_body = set_body.
  Hypothesis set_subvar : ∀ x (l : loc), x ≠ "args" → subst_var x l set_body = set_body.

  Hypothesis len_spec : ∀ g xs (a : val),
    R g xs a -∗
    WP App (Rec None (Some "a") len_body) (Val a)
      {{ v, ⌜ v = LitV (LitInt (Z.of_nat (length xs))) ⌝ ∗ R g xs a }}.
  Hypothesis get_spec : ∀ g xs (a : val) (i : nat) x,
    xs !! i = Some x →
    R g xs a -∗
    WP App (Rec None (Some "args") get_body)
         (Val (StructV [a; LitV (LitInt (Z.of_nat i))]))
      {{ v, ⌜ v = LitV (LitInt x) ⌝ ∗ R g xs a }}.
  Hypothesis set_spec : ∀ g xs (a : val) (i : nat) y x,
    xs !! i = Some y →
    R g xs a -∗
    WP App (Rec None (Some "args") set_body)
         (Val (StructV [a; LitV (LitInt (Z.of_nat i)); LitV (LitInt x)]))
      {{ v, ⌜ v = LitV LitUnit ⌝ ∗ R g (<[i := x]> xs) a }}.

  Lemma wp_struct_step vs v es Φ :
    WP Struct (vs ++ [v]) es {{ Φ }} ⊢ WP Struct vs (Val v :: es) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done| | |].
    { intros σ. eexists [], (Struct (vs ++ [v]) es), σ, []. constructor. }
    { intros ????? Hstep. inversion Hstep; simplify_eq; auto. }
    iIntros "!> _". iApply "H".
  Qed.

  Lemma wp_pack2 (v1 v2 : val) Φ :
    ▷ (£ 1 -∗ Φ (StructV [v1; v2])) ⊢
    WP Struct [] [Val v1; Val v2] {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_struct_step. iApply wp_struct_step. iApply wp_struct_done. iApply "H".
  Qed.

  Lemma wp_pack3 (v1 v2 v3 : val) Φ :
    ▷ (£ 1 -∗ Φ (StructV [v1; v2; v3])) ⊢
    WP Struct [] [Val v1; Val v2; Val v3] {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_struct_step. iApply wp_struct_step. iApply wp_struct_step.
    iApply wp_struct_done. iApply "H".
  Qed.

  Definition one : expr := Val (LitV (LitInt 1)).
  Definition zero : expr := Val (LitV (LitInt 0)).
  Definition unitv : expr := Val (LitV LitUnit).
  Definition plus1 (e : expr) : expr := BinOp PlusOp e one.
  Definition minus1 (e : expr) : expr := BinOp MinusOp e one.
  Definition zval (n : Z) : val := LitV (LitInt n).
  Definition nval (n : nat) : val := zval (Z.of_nat n).

  Definition call2 (body : expr) (a b : expr) (dst : string) (k : expr) : expr :=
    Let (Some "pack") (Struct [] [a; b])
      (Let (Some dst) (App (Rec None (Some "args") body) (Var "pack")) k).

  Definition call3 (body : expr) (a b c : expr) : expr :=
    Let (Some "pack") (Struct [] [a; b; c])
      (App (Rec None (Some "args") body) (Var "pack")).

  Definition call3_seq (body : expr) (a b c k : expr) : expr :=
    Let (Some "pack") (Struct [] [a; b; c])
      (Let None (App (Rec None (Some "args") body) (Var "pack")) k).

  Definition swap_body : expr :=
    Let (Some "a") (StructLoad (Var "args") 0)
    (Let (Some "i") (StructLoad (Var "args") 1)
    (Let (Some "j") (StructLoad (Var "args") 2)
      (call2 get_body (Var "a") (Var "i") "t"
        (call2 get_body (Var "a") (Var "j") "u"
          (call3_seq set_body (Var "a") (Var "i") (Var "u")
            (call3 set_body (Var "a") (Var "j") (Var "t"))))))).

  Definition call_swap (a : val) (i j : nat) : expr :=
    App (Val (RecV None (Some "args") swap_body))
      (Val (StructV [a; nval i; nval j])).

  Definition scan (a hi pivot : expr) : expr :=
    While (BinOp LeOp (plus1 (Var "j")) (minus1 hi))
      (call2 get_body a (Var "j") "v"
        (Let None
          (If (BinOp LeOp (Var "v") pivot)
            (Let None (call3 swap_body a (Var "i") (Var "j"))
              (Assign "i" (plus1 (Var "i"))))
            unitv)
          (Assign "j" (plus1 (Var "j"))))).

  Definition partition_body : expr :=
    Let (Some "a") (StructLoad (Var "args") 0)
    (Let (Some "lo") (StructLoad (Var "args") 1)
    (Let (Some "hi") (StructLoad (Var "args") 2)
      (call2 get_body (Var "a") (minus1 (Var "hi")) "pivot"
        (VarBind "i" (Var "lo")
          (VarBind "j" (Var "lo")
            (Let None (scan (Var "a") (Var "hi") (Var "pivot"))
              (Let None (call3 swap_body (Var "a") (Var "i") (minus1 (Var "hi")))
                (Var "i")))))))).

  Definition call_partition (a : val) (lo hi : nat) : expr :=
    App (Val (RecV None (Some "args") partition_body))
      (Val (StructV [a; nval lo; nval hi])).

  Definition qsort_body : expr :=
    Let (Some "a") (StructLoad (Var "args") 0)
    (Let (Some "lo") (StructLoad (Var "args") 1)
    (Let (Some "hi") (StructLoad (Var "args") 2)
      (If (BinOp LeOp (plus1 (Var "lo")) (minus1 (Var "hi")))
        (Let (Some "p")
          (App (Rec None (Some "args") partition_body)
            (Struct [] [Var "a"; Var "lo"; Var "hi"]))
          (Let None
            (App (Var "qsort") (Struct [] [Var "a"; Var "lo"; Var "p"]))
            (App (Var "qsort")
              (Struct [] [Var "a"; plus1 (Var "p"); Var "hi"]))))
        unitv))).

  Definition qsort_v : val := RecV (Some "qsort") (Some "args") qsort_body.

  Definition call_qsort (a : val) (lo hi : nat) : expr :=
    App (Val qsort_v) (Val (StructV [a; nval lo; nval hi])).

  Definition sort_body : expr :=
    Let (Some "n") (App (Rec None (Some "a") len_body) (Var "a"))
      (Let (Some "pack") (Struct [] [Var "a"; zero; Var "n"])
        (App (Rec (Some "qsort") (Some "args") qsort_body) (Var "pack"))).

  Definition call_sort (a : val) : expr :=
    App (Rec None (Some "a") sort_body) (Val a).

  Ltac restore :=
    repeat match goal with
    | |- context [subst ?x ?v get_body] => rewrite (get_sub x v); [|congruence]
    | |- context [subst ?x ?v set_body] => rewrite (set_sub x v); [|congruence]
    | |- context [subst ?x ?v len_body] => rewrite (len_sub x v); [|congruence]
    | |- context [subst_var ?x ?l get_body] => rewrite (get_subvar x l); [|congruence]
    | |- context [subst_var ?x ?l set_body] => rewrite (set_subvar x l); [|congruence]
    | |- context [subst_var ?x ?l len_body] => rewrite (len_subvar x l); [|congruence]
    end.

  Definition rigid (v : val) : Prop :=
    (∀ x w, subst_val x w v = v) ∧ (∀ x (l : loc), subst_var_val x l v = v).

  Ltac crunch Hsub :=
    unfold nval, zval, one, zero, unitv in *;
    cbn [subst subst_val subst_binder subst_var subst_var_val binds
         bool_decide String.eqb Ascii.eqb];
    repeat rewrite Hsub;
    restore.

  Ltac crunchv Hsub Hvar :=
    unfold nval, zval, one, zero, unitv in *;
    cbn [subst subst_val subst_binder subst_var subst_var_val binds
         bool_decide String.eqb Ascii.eqb];
    repeat rewrite Hsub; repeat rewrite Hvar; restore.

  Ltac solve_stable :=
    unfold swap_body, partition_body, qsort_body, sort_body, scan,
      call2, call3, call3_seq, plus1, minus1, one, zero, unitv;
    cbn [subst subst_var subst_binder binds];
    restore; reflexivity.

  Lemma swap_var_i (l : loc) : subst_var "i" l swap_body = swap_body.
  Proof. solve_stable. Qed.

  Lemma swap_var_j (l : loc) : subst_var "j" l swap_body = swap_body.
  Proof. solve_stable. Qed.

  Lemma swap_closed_v (w : val) : subst "v" w swap_body = swap_body.
  Proof. solve_stable. Qed.

  Lemma swap_closed_pack (w : val) : subst "pack" w swap_body = swap_body.
  Proof. solve_stable. Qed.

  Lemma swap_closed_a (w : val) : subst "a" w swap_body = swap_body.
  Proof. solve_stable. Qed.

  Lemma swap_closed_lo (w : val) : subst "lo" w swap_body = swap_body.
  Proof. solve_stable. Qed.

  Lemma swap_closed_hi (w : val) : subst "hi" w swap_body = swap_body.
  Proof. solve_stable. Qed.

  Lemma swap_closed_pivot (w : val) : subst "pivot" w swap_body = swap_body.
  Proof. solve_stable. Qed.

  Lemma swap_closed_p (w : val) : subst "p" w swap_body = swap_body.
  Proof. solve_stable. Qed.

  Lemma swap_closed_n (w : val) : subst "n" w swap_body = swap_body.
  Proof. solve_stable. Qed.

  Lemma part_closed_n (w : val) : subst "n" w partition_body = partition_body.
  Proof.
    unfold partition_body, scan, call2, call3, plus1, minus1, one, unitv.
    Opaque swap_body get_body set_body.
    simpl. restore. repeat rewrite swap_closed_n.
    Transparent swap_body get_body set_body.
    reflexivity.
  Qed.

  Lemma part_closed_pack (w : val) : subst "pack" w partition_body = partition_body.
  Proof.
    unfold partition_body, scan, call2, call3, plus1, minus1, one, unitv.
    Opaque swap_body get_body set_body.
    simpl. restore. repeat rewrite swap_closed_pack.
    Transparent swap_body get_body set_body.
    reflexivity.
  Qed.

  Lemma swap_closed_qsort (w : val) : subst "qsort" w swap_body = swap_body.
  Proof. solve_stable. Qed.

  Lemma swap_closed_i (w : val) : subst "i" w swap_body = swap_body.
  Proof. solve_stable. Qed.

  Lemma swap_closed_j (w : val) : subst "j" w swap_body = swap_body.
  Proof. solve_stable. Qed.

  Ltac names :=
    repeat match goal with
    | |- context [bool_decide (?x = ?y)] =>
        first [
          rewrite (bool_decide_eq_true_2 (x = y) eq_refl)
        | let Hneq := fresh "Hneq" in
          assert (x ≠ y) as Hneq by discriminate;
          rewrite (bool_decide_eq_false_2 (x = y) Hneq);
          clear Hneq ]
    end.

  Ltac crunchs Hsub :=
    repeat (progress (cbn [binds]; names; cbn [andb orb]; cbn iota;
          cbn [subst subst_binder subst_val subst_var_val];
          repeat rewrite Hsub;
          repeat rewrite swap_closed_v;
          repeat rewrite swap_closed_pack;
          repeat rewrite swap_closed_a;
          repeat rewrite swap_closed_lo;
          repeat rewrite swap_closed_hi;
          repeat rewrite swap_closed_pivot;
          repeat rewrite swap_closed_p;
          repeat rewrite swap_closed_n;
          repeat rewrite swap_closed_qsort;
          repeat rewrite swap_closed_i;
          repeat rewrite swap_closed_j;
          restore)).

  Definition slot (l : loc) : expr := Val (LitV (LitStack l)).
  Definition sload (l : loc) : expr := StackLoad (slot l).
  Definition sset (l : loc) (e : expr) : expr := StackAssign (slot l) e.

  Definition scan_open (a : val) (hi pivot : Z) (li lj : loc) : expr :=
    While (BinOp LeOp (plus1 (sload lj)) (minus1 (Val (zval hi))))
      (call2 get_body (Val a) (sload lj) "v"
        (Let None
          (If (BinOp LeOp (Var "v") (Val (zval pivot)))
            (Let None (call3 swap_body (Val a) (sload li) (sload lj))
              (sset li (plus1 (sload li))))
            unitv)
          (sset lj (plus1 (sload lj))))).

  Lemma scan_open_eq (a : val) (hi pivot : Z) (li lj : loc) :
    rigid a →
    subst_var "j" lj (subst_var "i" li
      (scan (Val a) (Val (zval hi)) (Val (zval pivot)))) =
    scan_open a hi pivot li lj.
  Proof.
    intros [Hsub Hvar].
    unfold scan, scan_open, call2, call3, plus1, minus1, sload, sset, slot.
    Opaque swap_body get_body set_body.
    repeat rewrite Hsub. repeat rewrite Hvar.
    simpl.
    repeat rewrite Hsub. repeat rewrite Hvar.
    repeat (rewrite (get_subvar _ li); [|discriminate]).
    repeat (rewrite (get_subvar _ lj); [|discriminate]).
    repeat (rewrite (set_subvar _ li); [|discriminate]).
    repeat (rewrite (set_subvar _ lj); [|discriminate]).
    repeat rewrite (swap_var_i li). repeat rewrite (swap_var_j lj).
    Transparent swap_body get_body set_body.
    reflexivity.
  Qed.

  Lemma swap_spec g xs (a : val) (i j : nat) xi xj :
    rigid a →
    xs !! i = Some xi → xs !! j = Some xj →
    R g xs a -∗
    WP call_swap a i j
      {{ v, ⌜ v = LitV LitUnit ⌝ ∗ R g (swap_list xs i j) a }}.
  Proof.
    iIntros (Hrigid Hi Hj) "Ha".
    destruct Hrigid as [Hsub _].
    unfold call_swap.
    iApply wp_app. unfold swap_body, call2, call3, call3_seq. crunch Hsub.
    set (arg := StructV [a; nval i; nval j]).
    unfold arg.
    iApply (wp_bind [LetCtx (Some "a")
      (Let (Some "i") (StructLoad (Val arg) 1)
        (Let (Some "j") (StructLoad (Val arg) 2)
          (Let (Some "pack") (Struct [] [Var "a"; Var "i"])
            (Let (Some "t")
              (App (Rec None (Some "args") get_body) (Var "pack"))
              (Let (Some "pack") (Struct [] [Var "a"; Var "j"])
                (Let (Some "u")
                  (App (Rec None (Some "args") get_body) (Var "pack"))
                  (Let (Some "pack") (Struct [] [Var "a"; Var "i"; Var "u"])
                    (Let None
                      (App (Rec None (Some "args") set_body) (Var "pack"))
                      (Let (Some "pack") (Struct [] [Var "a"; Var "j"; Var "t"])
                        (App (Rec None (Some "args") set_body)
                          (Var "pack")))))))))))]).
    iApply (wp_struct_load _ 0 a); [done|].
    iIntros "!> _". iApply wp_let. unfold arg. crunch Hsub.
    iApply (wp_bind [LetCtx (Some "i")
      (Let (Some "j") (StructLoad (Val arg) 2)
        (Let (Some "pack") (Struct [] [Val a; Var "i"])
          (Let (Some "t") (App (Rec None (Some "args") get_body) (Var "pack"))
            (Let (Some "pack") (Struct [] [Val a; Var "j"])
              (Let (Some "u") (App (Rec None (Some "args") get_body) (Var "pack"))
                (Let (Some "pack") (Struct [] [Val a; Var "i"; Var "u"])
                  (Let None (App (Rec None (Some "args") set_body) (Var "pack"))
                    (Let (Some "pack") (Struct [] [Val a; Var "j"; Var "t"])
                      (App (Rec None (Some "args") set_body) (Var "pack"))))))))))]).
    iApply (wp_struct_load _ 1 (nval i)); [done|].
    iIntros "!> _". iApply wp_let. crunch Hsub.
    iApply (wp_bind [LetCtx (Some "j")
      (Let (Some "pack") (Struct [] [Val a; Val (nval i)])
        (Let (Some "t") (App (Rec None (Some "args") get_body) (Var "pack"))
          (Let (Some "pack") (Struct [] [Val a; Var "j"])
            (Let (Some "u") (App (Rec None (Some "args") get_body) (Var "pack"))
              (Let (Some "pack") (Struct [] [Val a; Val (nval i); Var "u"])
                (Let None (App (Rec None (Some "args") set_body) (Var "pack"))
                  (Let (Some "pack") (Struct [] [Val a; Var "j"; Var "t"])
                    (App (Rec None (Some "args") set_body) (Var "pack")))))))))]).
    iApply (wp_struct_load _ 2 (nval j)); [done|].
    iIntros "!> _". iApply wp_let. crunch Hsub.
    iApply (wp_bind [LetCtx (Some "pack")
      (Let (Some "t") (App (Rec None (Some "args") get_body) (Var "pack"))
        (Let (Some "pack") (Struct [] [Val a; Val (nval j)])
          (Let (Some "u") (App (Rec None (Some "args") get_body) (Var "pack"))
            (Let (Some "pack") (Struct [] [Val a; Val (nval i); Var "u"])
              (Let None (App (Rec None (Some "args") set_body) (Var "pack"))
                (Let (Some "pack") (Struct [] [Val a; Val (nval j); Var "t"])
                  (App (Rec None (Some "args") set_body) (Var "pack"))))))))]).
    iApply wp_pack2. iIntros "!> _". iApply wp_let. crunch Hsub.
    set (s2 := StructV [a; nval i]).
    iApply (wp_bind [LetCtx (Some "t")
      (Let (Some "pack") (Struct [] [Val a; Val (nval j)])
        (Let (Some "u") (App (Rec None (Some "args") get_body) (Var "pack"))
          (Let (Some "pack") (Struct [] [Val a; Val (nval i); Var "u"])
            (Let None (App (Rec None (Some "args") set_body) (Var "pack"))
              (Let (Some "pack") (Struct [] [Val a; Val (nval j); Var "t"])
                (App (Rec None (Some "args") set_body) (Var "pack")))))))]).
    iApply (wp_wand with "[Ha]").
    { iApply (get_spec with "Ha"). exact Hi. }
    iIntros (v) "[%Hv Ha]". rewrite Hv. iApply wp_let. crunch Hsub.
    iApply (wp_bind [LetCtx (Some "pack")
      (Let (Some "u") (App (Rec None (Some "args") get_body) (Var "pack"))
        (Let (Some "pack") (Struct [] [Val a; Val (nval i); Var "u"])
          (Let None (App (Rec None (Some "args") set_body) (Var "pack"))
            (Let (Some "pack") (Struct [] [Val a; Val (nval j); Val (zval xi)])
              (App (Rec None (Some "args") set_body) (Var "pack"))))))]).
    iApply wp_pack2. iIntros "!> _". iApply wp_let. crunch Hsub.
    iApply (wp_bind [LetCtx (Some "u")
      (Let (Some "pack") (Struct [] [Val a; Val (nval i); Var "u"])
        (Let None (App (Rec None (Some "args") set_body) (Var "pack"))
          (Let (Some "pack") (Struct [] [Val a; Val (nval j); Val (zval xi)])
            (App (Rec None (Some "args") set_body) (Var "pack")))))]).
    iApply (wp_wand with "[Ha]").
    { iApply (get_spec with "Ha"). exact Hj. }
    iIntros (v2) "[%Hv2 Ha]". rewrite Hv2. iApply wp_let. crunch Hsub.
    iApply (wp_bind [LetCtx (Some "pack")
      (Let None (App (Rec None (Some "args") set_body) (Var "pack"))
        (Let (Some "pack") (Struct [] [Val a; Val (nval j); Val (zval xi)])
          (App (Rec None (Some "args") set_body) (Var "pack"))))]).
    iApply wp_pack3. iIntros "!> _". iApply wp_let. crunch Hsub.
    iApply (wp_bind [LetCtx None
      (Let (Some "pack") (Struct [] [Val a; Val (nval j); Val (zval xi)])
        (App (Rec None (Some "args") set_body) (Var "pack")))]).
    iApply (wp_wand with "[Ha]").
    { iApply (set_spec with "Ha"). exact Hi. }
    iIntros (v3) "[%Hv3 Ha]". rewrite Hv3. iApply wp_let. crunch Hsub.
    iApply (wp_bind [LetCtx (Some "pack")
      (App (Rec None (Some "args") set_body) (Var "pack"))]).
    iApply wp_pack3. iIntros "!> _". iApply wp_let. crunch Hsub.
    iApply (wp_wand with "[Ha]").
    { iApply (set_spec _ _ _ j with "Ha").
      destruct (decide (i = j)) as [->|Hne].
      - assert (xi = xj) as -> by congruence.
        rewrite list_lookup_insert; last (eapply lookup_lt_Some; exact Hj).
        done.
      - rewrite list_lookup_insert_ne; [exact Hj|exact Hne]. }
    iIntros (v4) "[%Hv4 Ha]". iSplit; [done|].
    rewrite (swap_list_code xs i j xi xj Hi Hj). done.
  Qed.

  Ltac take x :=
    match goal with
    | |- context [Let (Some x) ?e ?k] =>
        iApply (wp_bind [LetCtx (Some x) k])
    end.

  Ltac take_none :=
    match goal with
    | |- context [Let None ?e ?k] =>
        iApply (wp_bind [LetCtx None k])
    end.

  Lemma wp_scan_stop (a : val) (hi j : nat) (pivot : Z) (li lj : loc) Φ :
    (j = hi - 1)%nat →
    (0 < hi)%nat →
    StackId lj ↦ₛ LitV (LitInt (Z.of_nat j)) -∗
    (StackId lj ↦ₛ LitV (LitInt (Z.of_nat j)) -∗ Φ (LitV LitUnit)) -∗
    WP scan_open a (Z.of_nat hi) pivot li lj {{ Φ }}.
  Proof.
    iIntros (-> Hhi) "Hj HΦ".
    unfold scan_open, plus1, minus1, sload, slot, one.
    iApply wp_while.
    match goal with
    | |- context [If ?c ?e1 ?e2] =>
        iApply (wp_bind [IfCtx e1 e2])
    end.
    match goal with
    | |- context [BinOp LeOp ?e ?r] =>
        iApply (wp_bind [BinOpLCtx LeOp r])
    end.
    match goal with
    | |- context [BinOp PlusOp ?e ?r] =>
        iApply (wp_bind [BinOpLCtx PlusOp r])
    end.
    iApply (wp_stack_load (StackId lj) with "Hj").
    iIntros "!> _ Hj".
    iApply wp_binop; [simpl; reflexivity|].
    iIntros "!> _".
    simpl.
    match goal with
    | |- context [BinOp LeOp (Val ?lv) (BinOp MinusOp _ _)] =>
        iApply (wp_bind [BinOpRCtx LeOp lv])
    end.
    iApply wp_binop; [simpl; reflexivity|].
    iIntros "!> _".
    iApply wp_binop.
    { simpl. rewrite bool_decide_eq_false_2; [reflexivity|lia]. }
    iIntros "!> _".
    iApply wp_if_false.
    iApply wp_value'.
    iApply "HΦ". done.
  Qed.

  Lemma wp_inc (l : loc) (n : nat) Φ :
    StackId l ↦ₛ nval n -∗
    (StackId l ↦ₛ nval (S n) -∗ Φ (LitV LitUnit)) -∗
    WP sset l (plus1 (sload l)) {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    unfold sset, plus1, sload, slot, one, nval, zval.
    iApply (wp_bind [StackAssignRCtx (LitV (LitStack l))]).
    iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt 1)))]).
    iApply (wp_stack_load (StackId l) with "Hl").
    iIntros "!> _ Hl".
    iApply wp_binop; [simpl; reflexivity|].
    iIntros "!> _".
    assert (Z.of_nat n + 1 = Z.of_nat (S n))%Z as -> by lia.
    iApply (wp_stack_assign with "Hl").
    iIntros "!> _ Hl".
    iApply ("HΦ" with "Hl").
  Qed.

  Lemma wp_cons2 (a : val) (l : loc) (n : nat) Φ :
    StackId l ↦ₛ nval n -∗
    (StackId l ↦ₛ nval n -∗ ▷ (£ 1 -∗ Φ (StructV [a; nval n]))) -∗
    WP Struct [] [Val a; sload l] {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    unfold sload, slot, nval, zval.
    iApply wp_struct_step.
    iApply (wp_bind [StructCtx [a] []]).
    iApply (wp_stack_load (StackId l) with "Hl").
    iIntros "!> _ Hl".
    iApply wp_struct_step.
    iApply wp_struct_done.
    iApply ("HΦ" with "Hl").
  Qed.

  Lemma wp_cons3 (a : val) (li lj : loc) (i j : nat) Φ :
    StackId li ↦ₛ nval i -∗
    StackId lj ↦ₛ nval j -∗
    (StackId li ↦ₛ nval i -∗ StackId lj ↦ₛ nval j -∗
      ▷ (£ 1 -∗ Φ (StructV [a; nval i; nval j]))) -∗
    WP Struct [] [Val a; sload li; sload lj] {{ Φ }}.
  Proof.
    iIntros "Hi Hj HΦ".
    unfold sload, slot, nval, zval.
    iApply wp_struct_step.
    iApply (wp_bind [StructCtx [a] [sload lj]]).
    iApply (wp_stack_load (StackId li) with "Hi").
    iIntros "!> _ Hi".
    iApply wp_struct_step.
    iApply (wp_bind [StructCtx [a; nval i] []]).
    iApply (wp_stack_load (StackId lj) with "Hj").
    iIntros "!> _ Hj".
    iApply wp_struct_step.
    iApply wp_struct_done.
    iApply ("HΦ" with "Hi Hj").
  Qed.

  Definition scan_body (a : val) (pivot : Z) (li lj : loc) : expr :=
    call2 get_body (Val a) (sload lj) "v"
      (Let None
        (If (BinOp LeOp (Var "v") (Val (zval pivot)))
          (Let None (call3 swap_body (Val a) (sload li) (sload lj))
            (sset li (plus1 (sload li))))
          unitv)
        (sset lj (plus1 (sload lj)))).

  Lemma scan_body_eq (a : val) (hi pivot : Z) (li lj : loc) :
    scan_open a hi pivot li lj =
    While (BinOp LeOp (plus1 (sload lj)) (minus1 (Val (zval hi))))
      (scan_body a pivot li lj).
  Proof. reflexivity. Qed.

  Lemma wp_scan_body g xs (a : val) (pivot v xi : Z) (i j : nat) (li lj : loc) Φ :
    rigid a →
    xs !! i = Some xi →
    xs !! j = Some v →
    StackId li ↦ₛ nval i -∗
    StackId lj ↦ₛ nval j -∗
    R g xs a -∗
    (∀ xs' (i' : nat),
      ⌜if bool_decide (v ≤ pivot)%Z
       then xs' = swap_list xs i j ∧ i' = S i
       else xs' = xs ∧ i' = i⌝ -∗
      StackId li ↦ₛ nval i' -∗
      StackId lj ↦ₛ nval (S j) -∗
      R g xs' a -∗ Φ (LitV LitUnit)) -∗
    WP scan_body a pivot li lj {{ Φ }}.
  Proof.
    iIntros (Hrigid Hi Hj) "Hi Hj Ha HΦ".
    pose proof Hrigid as Hrig.
    destruct Hrigid as [Hsub _].
    unfold scan_body, call2, call3.
    Opaque swap_body.
    take "pack".
    iApply (wp_cons2 with "Hj").
    iIntros "Hj". iIntros "!> _".
    iApply wp_let. crunchs Hsub.
    take "v".
    iApply (wp_wand with "[Ha]").
    { iApply (get_spec with "Ha"). exact Hj. }
    iIntros (vv) "[%Hvv Ha]". rewrite Hvv. iApply wp_let. crunchs Hsub.
    take_none.
    match goal with
    | |- context [If ?c ?e1 ?e2] => iApply (wp_bind [IfCtx e1 e2])
    end.
    iApply wp_binop.
    { simpl. reflexivity. }
    iIntros "!> _".
    destruct (bool_decide (v ≤ pivot)%Z) eqn:Hcmp.
    - iApply wp_if_true.
      take_none.
      take "pack".
      iApply (wp_cons3 with "Hi Hj").
      iIntros "Hi Hj". iIntros "!> _".
      iApply wp_let. crunchs Hsub.
      iApply (wp_bind [AppLCtx (Val (StructV [a; nval i; nval j]))]).
      iApply wp_rec. iIntros "!> _".
      iApply (wp_wand with "[Ha]").
      { iApply (swap_spec with "Ha").
        - exact Hrig.
        - exact Hi.
        - exact Hj. }
      iIntros (su) "[%Hsu Ha]". rewrite Hsu. iApply wp_let. crunchs Hsub.
      iApply (wp_inc with "Hi").
      iIntros "Hi".
      iApply wp_let. crunchs Hsub.
      iApply (wp_inc with "Hj").
      iIntros "Hj".
      iApply ("HΦ" with "[] Hi Hj Ha").
      { iPureIntro. done. }
    - iApply wp_if_false.
      iApply wp_value'.
      iApply wp_let. crunchs Hsub.
      iApply (wp_inc with "Hj").
      iIntros "Hj".
      iApply ("HΦ" with "[] Hi Hj Ha").
      { iPureIntro. done. }
    Transparent swap_body.
  Qed.

  Lemma wp_scan n g xs (a : val) (hi : nat) (pivot : Z) (i j : nat) (li lj : loc) :
    rigid a →
    (0 < hi)%nat →
    ((hi - 1) - j = n)%nat →
    (j ≤ hi - 1)%nat →
    (i ≤ j)%nat →
    (hi - 1 < length xs)%nat →
    StackId li ↦ₛ nval i -∗
    StackId lj ↦ₛ nval j -∗
    R g xs a -∗
    WP scan_open a (Z.of_nat hi) pivot li lj
    {{ _, ∃ ys (p : nat),
        ⌜lomuto n xs pivot i j (hi - 1) = (ys, p)⌝ ∗
        StackId li ↦ₛ nval p ∗
        StackId lj ↦ₛ nval (hi - 1) ∗
        R g ys a }}.
  Proof.
    intros Hrigid Hhi. revert xs i j.
    induction n as [|n IH]; intros xs i j Hn Hjle Hile Hlen.
    - assert (j = hi - 1)%nat as -> by lia.
      iIntros "Hi Hj Ha".
      iApply (wp_scan_stop with "Hj"); [done|lia|].
      iIntros "Hj".
      iExists xs, i. simpl. iSplit; [done|]. iFrame.
    - assert (j < hi - 1)%nat as Hjb by lia.
      destruct (lookup_lt_is_Some_2 xs i) as [xi Hxi]; [lia|].
      destruct (lookup_lt_is_Some_2 xs j) as [vj Hvj]; [lia|].
      iIntros "Hi Hj Ha".
      remember (lomuto (S n) xs pivot i j (hi - 1)%nat) as spec eqn:Hspec.
      rewrite scan_body_eq.
      iApply wp_while.
      iApply (wp_bind [IfCtx
        (Seq (scan_body a pivot li lj)
          (While (BinOp LeOp (plus1 (sload lj)) (minus1 (Val (zval (Z.of_nat hi)))))
            (scan_body a pivot li lj)))
        (Val (LitV LitUnit))]).
      iApply (wp_bind [BinOpLCtx LeOp (minus1 (Val (zval (Z.of_nat hi))))]).
      iApply (wp_bind [BinOpLCtx PlusOp one]).
      iApply (wp_stack_load (StackId lj) with "Hj").
      iIntros "!> _ Hj".
      iApply wp_binop; [simpl; reflexivity|].
      iIntros "!> _".
      simpl. unfold minus1, one, zval.
      match goal with
      | |- context [BinOp LeOp (Val ?lv) (BinOp MinusOp _ _)] =>
          iApply (wp_bind [BinOpRCtx LeOp lv])
      end.
      iApply wp_binop; [simpl; reflexivity|].
      iIntros "!> _".
      iApply wp_binop.
      { simpl. rewrite bool_decide_eq_true_2; [reflexivity|lia]. }
      iIntros "!> _".
      iApply wp_if_true.
      iApply (wp_bind [SeqCtx
        (While (BinOp LeOp (plus1 (sload lj)) (minus1 (Val (zval (Z.of_nat hi)))))
          (scan_body a pivot li lj))]).
      iApply (wp_scan_body with "Hi Hj Ha").
      { exact Hrigid. }
      { exact Hxi. }
      { exact Hvj. }
      iIntros (xs' i') "%Hstep Hi Hj Ha".
      destruct (bool_decide (vj ≤ pivot)%Z) eqn:Hcmp.
      + simpl in Hstep. destruct Hstep as [-> ->].
        assert (spec = lomuto n (swap_list xs i j) pivot (S i) (S j) (hi - 1)) as ->.
        { rewrite Hspec. cbn [lomuto].
          assert (Nat.ltb j (hi - 1) = true) as -> by (apply Nat.ltb_lt; lia).
          rewrite Hvj.
          assert (Z.leb vj pivot = true) as ->.
          { apply bool_decide_eq_true_1 in Hcmp. apply Z.leb_le. exact Hcmp. }
          done. }
        assert ((hi - 1) < length (swap_list xs i j))%nat as Hlen'.
        { rewrite swap_list_length. exact Hlen. }
        iApply wp_seq.
        rewrite -scan_body_eq.
        iApply (IH (swap_list xs i j) (S i) (S j) with "Hi Hj Ha");
          [lia|lia|lia|exact Hlen'].
      + simpl in Hstep. destruct Hstep as [-> ->].
        assert (spec = lomuto n xs pivot i (S j) (hi - 1)) as ->.
        { rewrite Hspec. cbn [lomuto].
          assert (Nat.ltb j (hi - 1) = true) as -> by (apply Nat.ltb_lt; lia).
          rewrite Hvj.
          assert (Z.leb vj pivot = false) as ->.
          { apply Z.leb_gt. apply bool_decide_eq_false_1 in Hcmp. lia. }
          done. }
        iApply wp_seq.
        rewrite -scan_body_eq.
        iApply (IH xs i (S j) with "Hi Hj Ha"); [lia|lia|lia|exact Hlen].
  Qed.

  Definition part_tail (a : val) (hi : Z) (li : loc) : expr :=
    Let None (call3 swap_body (Val a) (sload li) (minus1 (Val (zval hi))))
      (sload li).

  Lemma part_tail_eq (a : val) (hi pivot : Z) (li lj : loc) :
    rigid a →
    subst_var "j" lj (subst_var "i" li
      (Let None (scan (Val a) (Val (zval hi)) (Val (zval pivot)))
        (Let None (call3 swap_body (Val a) (Var "i") (minus1 (Val (zval hi))))
          (Var "i")))) =
    Let None (scan_open a hi pivot li lj) (part_tail a hi li).
  Proof.
    intros [Hsub Hvar].
    unfold part_tail, scan, scan_open, call2, call3, plus1, minus1, sload, sset, slot.
    Opaque swap_body get_body set_body.
    repeat rewrite Hsub. repeat rewrite Hvar.
    simpl.
    repeat rewrite Hsub. repeat rewrite Hvar.
    repeat (rewrite (get_subvar _ li); [|discriminate]).
    repeat (rewrite (get_subvar _ lj); [|discriminate]).
    repeat (rewrite (set_subvar _ li); [|discriminate]).
    repeat (rewrite (set_subvar _ lj); [|discriminate]).
    repeat rewrite (swap_var_i li). repeat rewrite (swap_var_j lj).
    Transparent swap_body get_body set_body.
    reflexivity.
  Qed.

  Lemma partition_spec g xs (a : val) (lo hi : nat) (pivot : Z) :
    rigid a →
    (lo < hi)%nat →
    (hi ≤ length xs)%nat →
    xs !! (hi - 1)%nat = Some pivot →
    R g xs a -∗
    WP call_partition a lo hi
    {{ v, ∃ ys (p : nat),
        ⌜partition_list xs lo hi = (ys, p)⌝ ∗
        ⌜v = nval p⌝ ∗
        R g ys a }}.
  Proof.
    iIntros (Hrigid Hlt Hlen Hpivot) "Ha".
    pose proof Hrigid as Hrig. destruct Hrigid as [Hsub Hvar].
    unfold call_partition.
    Opaque swap_body.
    iApply wp_app. unfold partition_body, call2, call3. crunchs Hsub.
    take "a".
    iApply (wp_struct_load _ 0 a); [done|].
    iIntros "!> _". iApply wp_let. crunchs Hsub.
    take "lo".
    iApply (wp_struct_load _ 1 (nval lo)); [done|].
    iIntros "!> _". iApply wp_let. crunchs Hsub.
    take "hi".
    iApply (wp_struct_load _ 2 (nval hi)); [done|].
    iIntros "!> _". iApply wp_let. crunchs Hsub.
    take "pack".
    iApply wp_struct_step.
    iApply (wp_bind [StructCtx [a] []]).
    unfold minus1, one, zval, nval.
    iApply wp_binop; [simpl; reflexivity|].
    iIntros "!> _".
    assert ((Z.of_nat hi - 1)%Z = Z.of_nat (hi - 1)) as -> by lia.
    iApply wp_struct_step. iApply wp_struct_done.
    iIntros "!> _". iApply wp_let. crunchs Hsub.
    take "pivot".
    iApply (wp_wand with "[Ha]").
    { iApply (get_spec with "Ha"). exact Hpivot. }
    iIntros (vp) "[%Hvp Ha]". rewrite Hvp. iApply wp_let. crunchs Hsub.
    simpl. restore. repeat rewrite Hsub.
    repeat rewrite swap_closed_a. repeat rewrite swap_closed_lo.
    repeat rewrite swap_closed_hi. repeat rewrite swap_closed_pivot.
    repeat rewrite swap_closed_pack. repeat rewrite swap_closed_v.
    iApply wp_var_bind. iIntros (li) "Hi".
    repeat (progress (cbn [subst_var subst_var_val binds]; names;
      cbn [andb orb]; cbn iota)).
    iApply wp_var_bind. iIntros (lj) "Hj".
    repeat (progress (cbn [subst_var subst_var_val binds]; names;
      cbn [andb orb]; cbn iota)).
    repeat (rewrite (get_subvar _ li); [|discriminate]).
    repeat (rewrite (get_subvar _ lj); [|discriminate]).
    repeat (rewrite (set_subvar _ li); [|discriminate]).
    repeat (rewrite (set_subvar _ lj); [|discriminate]).
    repeat rewrite (swap_var_i li). repeat rewrite (swap_var_j lj).
    repeat rewrite Hsub. repeat rewrite Hvar.
    match goal with
    | |- context [Let None (While ?c ?b) ?k] =>
        replace (Let None (While c b) k)
          with (Let None (scan_open a (Z.of_nat hi) pivot li lj)
                 (part_tail a (Z.of_nat hi) li))
          by reflexivity
    end.
    iApply (wp_bind [LetCtx None (part_tail a (Z.of_nat hi) li)]).
    iApply (wp_wand with "[Hi Hj Ha]").
    { iApply (wp_scan ((hi - 1) - lo) _ _ _ hi pivot lo lo with "Hi Hj Ha").
      - exact Hrig.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia. }
    iIntros (vu) "Hscan".
    iDestruct "Hscan" as (ys q) "(%Hlom & Hi & Hj & Ha)".
    assert (lo ≤ hi - 1)%nat as Hlo by lia.
    assert (hi - 1 < length xs)%nat as Hbound by lia.
    pose proof (lomuto_inv_start xs lo (hi - 1) pivot Hlo Hbound Hpivot) as Hstart.
    assert (((hi - 1) - lo) = (hi - 1) - lo)%nat as Hfuel by lia.
    pose proof (lomuto_go ((hi - 1) - lo) xs xs lo lo lo (hi - 1) pivot ys q
                  Hstart Hfuel Hlom) as Hdone.
    destruct (lookup_lt_is_Some_2 ys q) as [xq Hxq].
    { pose proof (linv_ij _ _ _ _ _ _ _ Hdone) as Hij.
      pose proof (linv_lenb _ _ _ _ _ _ _ Hdone) as Hlb. lia. }
    iApply wp_let.
    unfold part_tail, call3.
    take_none.
    take "pack".
    iApply wp_struct_step.
    iApply (wp_bind [StructCtx [a] [minus1 (Val (zval (Z.of_nat hi)))]]).
    iApply (wp_stack_load (StackId li) with "Hi").
    iIntros "!> _ Hi".
    iApply wp_struct_step.
    iApply (wp_bind [StructCtx [a; nval q] []]).
    unfold minus1, one, zval.
    iApply wp_binop; [simpl; reflexivity|].
    iIntros "!> _".
    assert ((Z.of_nat hi - 1)%Z = Z.of_nat (hi - 1)) as -> by lia.
    iApply wp_struct_step. iApply wp_struct_done.
    iIntros "!> _". iApply wp_let. crunchs Hsub.
    iApply (wp_bind [AppLCtx (Val (StructV [a; nval q; nval (hi - 1)]))]).
    iApply wp_rec. iIntros "!> _".
    iApply (wp_wand with "[Ha]").
    { iApply (swap_spec with "Ha").
      - exact Hrig.
      - exact Hxq.
      - pose proof (linv_piv _ _ _ _ _ _ _ Hdone) as Hpiv. exact Hpiv. }
    iIntros (su) "[%Hsu Ha]". rewrite Hsu. iApply wp_let. crunchs Hsub.
    iApply (wp_stack_load (StackId li) with "Hi").
    iIntros "!> _ Hi".
    iExists (nval (hi - 1)). iFrame "Hj".
    iExists (nval q). iFrame "Hi".
    iExists (swap_list ys q (hi - 1)), q.
    iSplit.
    { iPureIntro. unfold partition_list. rewrite Hpivot. rewrite Hlom. done. }
    iSplit; [done|]. done.
    Transparent swap_body.
  Qed.

  Lemma wp_qslice n g xs (a : val) (lo hi : nat) :
    rigid a →
    (hi ≤ length xs)%nat →
    (hi - lo ≤ n)%nat →
    R g xs a -∗
    WP call_qsort a lo hi {{ _, R g (qsort_slice n xs lo hi) a }}.
  Proof.
    intros Hrigid. revert xs lo hi. induction n as [|n IH]; intros xs lo hi Hlen Hfuel.
    - assert (hi ≤ lo)%nat as Hshort by lia.
      iIntros "Ha".
      pose proof Hrigid as Hrig. destruct Hrigid as [Hsub Hvar].
      unfold call_qsort, qsort_v.
      Opaque swap_body partition_body.
      iApply wp_app. unfold qsort_body. crunchs Hsub.
      simpl. restore. repeat rewrite Hsub. repeat rewrite Hvar.
      take "a". iApply (wp_struct_load _ 0 a); [done|].
      iIntros "!> _". iApply wp_let. crunchs Hsub.
      take "lo". iApply (wp_struct_load _ 1 (nval lo)); [done|].
      iIntros "!> _". iApply wp_let. crunchs Hsub.
      take "hi". iApply (wp_struct_load _ 2 (nval hi)); [done|].
      iIntros "!> _". iApply wp_let. crunchs Hsub.
      match goal with
      | |- context [If ?c ?e1 ?e2] => iApply (wp_bind [IfCtx e1 e2])
      end.
      iApply (wp_bind [BinOpLCtx LeOp (minus1 (Val (nval hi)))]).
      unfold plus1, one, nval, zval.
      iApply wp_binop; [simpl; reflexivity|].
      iIntros "!> _".
      simpl. unfold minus1, one.
      match goal with
      | |- context [BinOp LeOp (Val ?lv) (BinOp MinusOp _ _)] =>
          iApply (wp_bind [BinOpRCtx LeOp lv])
      end.
      iApply wp_binop; [simpl; reflexivity|].
      iIntros "!> _".
      iApply wp_binop.
      { simpl. rewrite bool_decide_eq_false_2; [reflexivity|lia]. }
      iIntros "!> _".
      iApply wp_if_false. iApply wp_value'.
      simpl. done.
      Transparent swap_body partition_body.
    - iIntros "Ha".
      remember (qsort_slice (S n) xs lo hi) as spec eqn:Hspec.
      pose proof Hrigid as Hrig. destruct Hrigid as [Hsub Hvar].
      unfold call_qsort, qsort_v.
      Opaque swap_body partition_body.
      iApply wp_app. unfold qsort_body. crunchs Hsub.
      simpl. restore. repeat rewrite Hsub. repeat rewrite Hvar.
      take "a". iApply (wp_struct_load _ 0 a); [done|].
      iIntros "!> _". iApply wp_let. crunchs Hsub.
      take "lo". iApply (wp_struct_load _ 1 (nval lo)); [done|].
      iIntros "!> _". iApply wp_let. crunchs Hsub.
      take "hi". iApply (wp_struct_load _ 2 (nval hi)); [done|].
      iIntros "!> _". iApply wp_let. crunchs Hsub.
      match goal with
      | |- context [If ?c ?e1 ?e2] => iApply (wp_bind [IfCtx e1 e2])
      end.
      iApply (wp_bind [BinOpLCtx LeOp (minus1 (Val (nval hi)))]).
      unfold plus1, one, nval, zval.
      iApply wp_binop; [simpl; reflexivity|].
      iIntros "!> _".
      simpl. unfold minus1, one.
      match goal with
      | |- context [BinOp LeOp (Val ?lv) (BinOp MinusOp _ _)] =>
          iApply (wp_bind [BinOpRCtx LeOp lv])
      end.
      iApply wp_binop; [simpl; reflexivity|].
      iIntros "!> _".
      destruct (Nat.leb hi (lo + 1)%nat) eqn:Hshort.
      + iApply wp_binop.
        { simpl. rewrite bool_decide_eq_false_2; [reflexivity|].
          apply Nat.leb_le in Hshort. lia. }
        iIntros "!> _".
        iApply wp_if_false. iApply wp_value'.
        rewrite Hspec. simpl. rewrite Hshort. done.
        Transparent swap_body partition_body.
      + iApply wp_binop.
        { simpl. rewrite bool_decide_eq_true_2; [reflexivity|].
          apply Nat.leb_gt in Hshort. lia. }
        iIntros "!> _".
        iApply wp_if_true.
        take "p".
        iApply (wp_bind [AppLCtx (Struct [] [Val a; Val (nval lo); Val (nval hi)])]).
        iApply wp_rec. iIntros "!> _".
        simpl.
        match goal with
        | |- context [App (Val ?f) (Struct [] [Val a; Val (nval lo); Val (nval hi)])] =>
            iApply (wp_bind [AppRCtx f])
        end.
        iApply wp_pack3. iIntros "!> _".
        simpl. restore.
        repeat rewrite swap_closed_qsort.
        match goal with
        | |- context [App (Val ?f) (Val ?sv)] =>
            replace (App (Val f) (Val sv)) with (call_partition a lo hi)
              by reflexivity
        end.
        assert (lo < hi)%nat as Hlt.
        { apply Nat.leb_gt in Hshort. lia. }
        destruct (lookup_lt_is_Some_2 xs (hi - 1)) as [pivot Hpivot]; [lia|].
        iApply (wp_wand with "[Ha]").
        { iApply (partition_spec with "Ha").
          - exact Hrig.
          - exact Hlt.
          - exact Hlen.
          - exact Hpivot. }
        iIntros (vp) "Hp".
        iDestruct "Hp" as (ys p) "(%Hpart & %Hvp & Ha)".
        rewrite Hvp. iApply wp_let. crunchs Hsub.
        destruct (partition_list_ok xs lo hi ys p Hlt Hlen Hpart)
          as [pivot' [Hleny [Hperm [Hrange _]]]].
        destruct Hrange as [Hplo Hphi].
        assert (p - lo ≤ n)%nat as Hfuel1 by lia.
        assert (p ≤ length ys)%nat as Hlenp by lia.
        match goal with
        | |- context [Let None ?e ?k] => iApply (wp_bind [LetCtx None k])
        end.
        match goal with
        | |- context [App (Val ?f) ?arg] => iApply (wp_bind [AppRCtx f])
        end.
        iApply wp_pack3. iIntros "!> _".
        simpl. restore.
        match goal with
        | |- context [App (Val ?f) (Val ?sv)] =>
            replace (App (Val f) (Val sv)) with (call_qsort a lo p) by reflexivity
        end.
        iApply (wp_wand with "[Ha]").
        { iApply (IH ys lo p with "Ha"); [lia|exact Hfuel1]. }
        iIntros (u1) "Ha".
        iApply wp_let. crunchs Hsub.
        assert (hi - S p ≤ n)%nat as Hfuel2 by lia.
        assert (hi ≤ length (qsort_slice n ys lo p))%nat as Hlen2.
        { destruct (qsort_slice_spec n ys lo p Hlenp Hfuel1) as [Hly _].
          rewrite Hly Hleny. exact Hlen. }
        set (ys1 := qsort_slice n ys lo p) in *.
        match goal with
        | |- context [App (Val ?f) ?arg] => iApply (wp_bind [AppRCtx f])
        end.
        iApply wp_struct_step.
        iApply (wp_bind [StructCtx [a] [Val (nval hi)]]).
        unfold plus1, one, nval, zval.
        iApply wp_binop; [simpl; reflexivity|].
        iIntros "!> _".
        assert ((Z.of_nat p + 1)%Z = Z.of_nat (S p)) as -> by lia.
        iApply wp_struct_step. iApply wp_struct_step. iApply wp_struct_done.
        iIntros "!> _".
        assert (spec = qsort_slice n ys1 (S p) hi) as ->.
        { rewrite Hspec. simpl. rewrite Hshort. rewrite Hpart. simpl.
          unfold ys1. done. }
        iApply (IH ys1 (S p) hi with "Ha"); [exact Hlen2|exact Hfuel2].
        Transparent swap_body partition_body.
  Qed.

  Lemma sort_spec g xs (a : val) :
    rigid a →
    R g xs a -∗
    WP call_sort a {{ _, R g (qsort xs) a }}.
  Proof.
    iIntros (Hrigid) "Ha".
    pose proof Hrigid as Hrig. destruct Hrigid as [Hsub Hvar].
    unfold call_sort.
    iApply (wp_bind [AppLCtx (Val a)]).
    iApply wp_rec. iIntros "!> _".
    Opaque swap_body partition_body.
    iApply wp_app. unfold sort_body. crunchs Hsub.
    simpl. restore. repeat rewrite Hsub. repeat rewrite Hvar.
    take "n".
    iApply (wp_wand with "[Ha]").
    { iApply (len_spec with "Ha"). }
    iIntros (vn) "[%Hn Ha]". rewrite Hn. iApply wp_let. crunchs Hsub.
    take "pack".
    unfold zero, nval, zval.
    iApply wp_pack3. iIntros "!> _".
    iApply wp_let. crunchs Hsub.
    simpl. restore. repeat rewrite Hsub. repeat rewrite Hvar.
    match goal with
    | |- context [App (Rec ?f ?x ?body) (Val ?sv)] =>
        iApply (wp_bind [AppLCtx (Val sv)]);
        iApply wp_rec; iIntros "!> _"
    end.
    simpl. restore.
    repeat rewrite part_closed_n. repeat rewrite part_closed_pack.
    repeat rewrite swap_closed_n. repeat rewrite swap_closed_pack.
    match goal with
    | |- context [App (Val ?fv) (Val ?sv)] =>
        replace (App (Val fv) (Val sv))
          with (call_qsort a 0%nat (length xs)) by reflexivity
    end.
    rewrite /qsort.
    iApply (wp_qslice (length xs) with "Ha").
    - exact Hrig.
    - lia.
    - lia.
    Transparent swap_body partition_body.
  Qed.

End qsort_alg.

(** * The two arrays

Each instance only supplies the three library specifications. The
representation predicate is opened far enough to see that the value is a
literal, which is what makes it rigid, and is then rebuilt. *)

Section instances.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  Ltac closed_sub Hx :=
    repeat (progress (
      simpl;
      first [
        rewrite (bool_decide_eq_false_2 _ Hx)
      | match goal with
        | |- context [bool_decide (?u = ?y)] => destruct (bool_decide (u = y))
        end
      ];
      cbn iota));
    reflexivity.

  Lemma lit_rigid (b : base_lit) : rigid (LitV b).
  Proof. split; intros; reflexivity. Qed.

  Lemma array_qsort_spec xs (a : val) :
    is_array xs a -∗
    WP call_sort length_body get_body set_body a
      {{ _, is_array (qsort xs) a }}.
  Proof.
    iIntros "Ha".
    iDestruct "Ha" as (o base) "(%Ha & Hlen & Hptr & Hblk & Hcells)".
    rewrite Ha.
    iApply (wp_wand with "[Hlen Hptr Hblk Hcells]").
    { iApply (sort_spec unit (λ _ ys b, is_array ys b)
          length_body get_body set_body with "[Hlen Hptr Hblk Hcells]").
      - intros x v Hx. closed_sub Hx.
      - intros x l Hx. closed_sub Hx.
      - intros x v Hx. closed_sub Hx.
      - intros x l Hx. closed_sub Hx.
      - intros x v Hx. closed_sub Hx.
      - intros x l Hx. closed_sub Hx.
      - intros _ xs0 a0. iApply length_spec.
      - intros _ xs0 a0 i x Hi. iApply get_spec. exact Hi.
      - intros _ xs0 a0 i y x Hi. iApply set_spec. exact Hi.
      - apply lit_rigid.
      - iExists o, base. iSplit; [done|]. iFrame. }
    iIntros (v) "Ha". done.
    Unshelve. exact tt.
  Qed.

  Lemma arraylist_qsort_at (g : nat * Z) xs (a : val) :
    is_arraylist xs (fst g) (snd g) a -∗
    WP call_sort size_body al_get_body al_set_body a
      {{ _, is_arraylist (qsort xs) (fst g) (snd g) a }}.
  Proof.
    iIntros "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    rewrite Ha.
    iApply (wp_wand with "[Hbuf Hsz Hver Hdata]").
    { iApply (sort_spec (nat * Z) (λ g' ys b,
          is_arraylist ys (fst g') (snd g') b)
          size_body al_get_body al_set_body with "[Hbuf Hsz Hver Hdata]").
      - intros x v Hx. closed_sub Hx.
      - intros x l Hx. closed_sub Hx.
      - intros x v Hx. closed_sub Hx.
      - intros x l Hx. closed_sub Hx.
      - intros x v Hx. closed_sub Hx.
      - intros x l Hx. closed_sub Hx.
      - intros [cap0 ver0] xs0 a0. iApply size_spec.
      - intros [cap0 ver0] xs0 a0 i x Hi. iApply al_get_spec. exact Hi.
      - intros [cap0 ver0] xs0 a0 i y x Hi. iApply al_set_spec. exact Hi.
      - apply lit_rigid.
      - unfold is_arraylist. iExists o, buf. iFrame "Hbuf Hsz Hver Hdata".
        iPureIntro. split; [done|]. split; [exact Hlen|]. exact Hcap. }
    iIntros (v) "Ha". done.
  Qed.

  Lemma arraylist_qsort_spec xs cap ver (a : val) :
    is_arraylist xs cap ver a -∗
    WP call_sort size_body al_get_body al_set_body a
      {{ _, is_arraylist (qsort xs) cap ver a }}.
  Proof. exact (arraylist_qsort_at (cap, ver) xs a). Qed.

End instances.
