(** Hash maps, lowered from Cangjie [HashMap] to monomorphic [Int64] keys
and values.

The library stores entries in a bucket array and an entry array. An entry
with hash [-1] is empty; a deleted entry sits on a free list. The load
limit is three quarters, and growth uses a shift to reach one and a half
times the old capacity. A raw cell of this language holds one integer, and
the operators are addition, subtraction, and comparison, so the table here
is three arrays from the array library: a tag, a key, and a value. Tag [0]
is empty, which is what allocation writes; tag [1] is occupied; tag [2] is
a deleted slot. The bucket is the non-negative remainder of the key by the
capacity, computed by adding or subtracting the capacity, and the table
doubles, by adding the capacity to itself, when [size + size] reaches the
capacity. Both agree with a power-of-two mask and a load of one half.
Lookup walks from that bucket, skips deleted slots, and stops at an empty
slot or a matching key, wrapping at most once. Insertion reuses the first
deleted slot on that walk. A missing key is a struct of a boolean and an
integer whose flag is false, not a stuck load. *)

From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws.
From cjr.examples Require Import array hm_tactics.
From iris.prelude Require Import options.
From Coq Require Import Lia PeanoNat Wf_nat.
Close Scope expr_scope.

Definition default_capacity : nat := 16.

(** * Tags, remainder, and slots *)

Definition tag_empty : Z := 0.
Definition tag_occ : Z := 1.
Definition tag_tomb : Z := 2.

Definition tag_ok (t : Z) : Prop :=
  t = tag_empty \/ t = tag_occ \/ t = tag_tomb.
Definition tags_ok (tags : list Z) : Prop := Forall tag_ok tags.

Lemma tags_ok_lookup tags i t :
  tags_ok tags → tags !! i = Some t → tag_ok t.
Proof. intros Hok Hi. by eapply Forall_lookup_1. Qed.

(** Bring a negative representative up to zero by adding the capacity,
then bring a representative that is at least the capacity down by
subtracting it. The fuel is the value itself, so each step is smaller. *)

Fixpoint bring_nonneg (fuel : nat) (h cap : Z) : Z :=
  match fuel with
  | O => h
  | S fuel =>
      if decide (h < 0)%Z then bring_nonneg fuel (h + cap)%Z cap else h
  end.

Fixpoint bring_below (fuel : nat) (h cap : Z) : Z :=
  match fuel with
  | O => h
  | S fuel =>
      if decide (cap ≤ h)%Z then bring_below fuel (h - cap)%Z cap else h
  end.

Definition residue (k cap : Z) : Z :=
  let h := bring_nonneg (Z.to_nat (Z.max 0 (- k))) k cap in
  bring_below (Z.to_nat h) h cap.

Lemma z_to_nat_0 n : (Z.to_nat n = 0)%nat → (n ≤ 0)%Z.
Proof. destruct n; simpl; lia. Qed.

Lemma bring_nonneg_spec h cap fuel :
  (0 < cap)%Z →
  (Z.to_nat (Z.max 0 (- h)) ≤ fuel)%nat →
  (0 ≤ bring_nonneg fuel h cap)%Z ∧
  Z.modulo (bring_nonneg fuel h cap) cap = Z.modulo h cap.
Proof.
  revert h. induction fuel as [|fuel IH]; intros h Hcap Hfuel; simpl.
  - assert (Z.to_nat (Z.max 0 (- h)) = 0)%nat as Hz.
    { destruct (Z.to_nat (Z.max 0 (- h))) as [|n]; [done|lia]. }
    apply z_to_nat_0 in Hz.
    assert ((- h) ≤ 0)%Z.
    { destruct (Z.max_spec 0 (- h)) as [[Hm Heq]|[Hm Heq]]; lia. }
    split; [lia|done].
  - destruct (decide (h < 0)%Z) as [Hn|Hn].
    + destruct (IH (h + cap)%Z) as [H0 Hmod]; [done| |].
      * assert (0 < cap)%Z as Hpos by done.
        destruct (Z_lt_le_dec (h + cap) 0) as [Hstill|Hdone].
        -- assert (Z.max 0 (- (h + cap)) = (- h - cap))%Z as ->.
           { rewrite Z.max_r; lia. }
           assert (Z.max 0 (- h) = (- h))%Z as Heq.
           { rewrite Z.max_r; lia. }
           rewrite Heq in Hfuel.
           replace (Z.to_nat (- h)) with
             (Z.to_nat (- h - cap) + Z.to_nat cap)%nat in Hfuel.
           { assert ((1 ≤ Z.to_nat cap)%nat) as Hone.
             { replace 1%nat with (Z.to_nat 1%Z) by reflexivity.
               apply Z2Nat.inj_le; lia. }
             lia. }
           { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
        -- assert (Z.max 0 (- (h + cap)) = 0)%Z as -> by (rewrite Z.max_l; lia).
           simpl. lia.
      * split; [done|]. rewrite Hmod.
        replace (h + cap)%Z with (h + 1 * cap)%Z by lia.
        rewrite Z.mod_add; lia.
    + split; [lia|done].
Qed.

Lemma bring_below_spec h cap fuel :
  (0 < cap)%Z →
  (0 ≤ h)%Z →
  (Z.to_nat h ≤ fuel)%nat →
  (0 ≤ bring_below fuel h cap < cap)%Z ∧
  Z.modulo (bring_below fuel h cap) cap = Z.modulo h cap.
Proof.
  revert h. induction fuel as [|fuel IH]; intros h Hcap Hnn Hfuel; simpl.
  - assert (Z.to_nat h = 0)%nat as Hz.
    { destruct (Z.to_nat h) as [|n]; [done|lia]. }
    apply z_to_nat_0 in Hz. split; [lia|]. rewrite Z.mod_small; lia.
  - destruct (decide (cap ≤ h)%Z) as [Hge|Hlt].
    + destruct (IH (h - cap)%Z) as [Hrng Hmod]; [done|lia| |].
      * replace (Z.to_nat h) with (Z.to_nat (h - cap) + Z.to_nat cap)%nat in Hfuel.
        { assert ((1 ≤ Z.to_nat cap)%nat) as Hone.
          { replace 1%nat with (Z.to_nat 1%Z) by reflexivity.
            apply Z2Nat.inj_le; lia. }
          lia. }
        { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
      * split; [done|]. rewrite Hmod.
        replace (h - cap)%Z with (h + (-1) * cap)%Z by lia.
        rewrite Z.mod_add; lia.
    + split; [lia|]. rewrite Z.mod_small; lia.
Qed.

Lemma bring_nonneg_ge h cap fuel :
  (0 < cap)%Z →
  (Z.to_nat (Z.max 0 (- h)) ≤ fuel)%nat →
  bring_nonneg fuel h cap = bring_nonneg (Z.to_nat (Z.max 0 (- h))) h cap.
Proof.
  intros Hcap Hle. revert h Hle.
  induction fuel as [fuel IH] using lt_wf_ind. intros h Hle.
  destruct fuel as [|fuel].
  - assert (Z.to_nat (Z.max 0 (- h)) = 0)%nat as -> by lia. reflexivity.
  - simpl. destruct (decide (h < 0)%Z) as [Hn|Hp].
    + assert (Z.max 0 (- h) = - h)%Z as Hm by (rewrite Z.max_r; lia).
      rewrite Hm in Hle.
      assert (0 < Z.to_nat (- h))%nat as Hpos.
      { apply Nat.neq_0_lt_0. intros Hz. apply z_to_nat_0 in Hz. lia. }
      rewrite Hm.
      assert (Z.to_nat (- h) = S (Nat.pred (Z.to_nat (- h)))) as -> by lia.
      simpl. destruct (decide (h < 0)%Z); [|lia].
      assert (Z.to_nat (Z.max 0 (- (h + cap))) ≤ fuel)%nat as Hfuel.
      { destruct (Z_lt_le_dec (h + cap) 0) as [Hstill|Hdone].
        - assert (Z.max 0 (- (h + cap)) = (- h - cap))%Z as -> by (rewrite Z.max_r; lia).
          assert (Z.to_nat (- h) = (Z.to_nat (- h - cap) + Z.to_nat cap)%nat) as Hsum.
          { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
          assert (1 ≤ Z.to_nat cap)%nat as Hone.
          { replace 1%nat with (Z.to_nat 1%Z) by reflexivity.
            apply Z2Nat.inj_le; lia. }
          lia.
        - assert (Z.max 0 (- (h + cap)) = 0)%Z as -> by (rewrite Z.max_l; lia). lia. }
      assert (Z.to_nat (Z.max 0 (- (h + cap))) ≤ Nat.pred (Z.to_nat (- h)))%nat as Hpred.
      { destruct (Z_lt_le_dec (h + cap) 0) as [Hstill|Hdone].
        - assert (Z.max 0 (- (h + cap)) = (- h - cap))%Z as -> by (rewrite Z.max_r; lia).
          assert (Z.to_nat (- h) = (Z.to_nat (- h - cap) + Z.to_nat cap)%nat) as Hsum.
          { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
          assert (1 ≤ Z.to_nat cap)%nat as Hone.
          { replace 1%nat with (Z.to_nat 1%Z) by reflexivity.
            apply Z2Nat.inj_le; lia. }
          lia.
        - assert (Z.max 0 (- (h + cap)) = 0)%Z as -> by (rewrite Z.max_l; lia). lia. }
      assert (fuel < S fuel)%nat as Hlt by lia.
      assert (Nat.pred (Z.to_nat (- h)) < S fuel)%nat as Hlt2 by lia.
      rewrite (IH fuel Hlt (h + cap)%Z Hfuel).
      rewrite (IH (Nat.pred (Z.to_nat (- h))) Hlt2 (h + cap)%Z Hpred).
      reflexivity.
    + assert (Z.max 0 (- h) = 0)%Z as -> by (rewrite Z.max_l; lia). reflexivity.
Qed.

Lemma bring_below_ge h cap fuel :
  (0 < cap)%Z → (0 ≤ h)%Z →
  (Z.to_nat h ≤ fuel)%nat →
  bring_below fuel h cap = bring_below (Z.to_nat h) h cap.
Proof.
  intros Hcap Hnn Hle. revert h Hnn Hle.
  induction fuel as [fuel IH] using lt_wf_ind. intros h Hnn Hle.
  destruct fuel as [|fuel].
  - assert (Z.to_nat h = 0)%nat as -> by lia. reflexivity.
  - simpl. destruct (decide (cap ≤ h)%Z) as [Hge|Hlt].
    + assert (0 < Z.to_nat h)%nat as Hpos.
      { apply Nat.neq_0_lt_0. intros Hz. apply z_to_nat_0 in Hz. lia. }
      set (p := Nat.pred (Z.to_nat h)).
      assert (Z.to_nat h = S p) as Hs by (unfold p; lia).
      rewrite Hs. simpl. destruct (decide (cap ≤ h)%Z); [|lia].
      assert (0 ≤ h - cap)%Z as Hnn' by lia.
      assert (Z.to_nat (h - cap) ≤ fuel)%nat as Hle1.
      { assert (Z.to_nat h = (Z.to_nat (h - cap) + Z.to_nat cap)%nat) as Hsum.
        { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
        assert (1 ≤ Z.to_nat cap)%nat as Hone.
        { replace 1%nat with (Z.to_nat 1%Z) by reflexivity.
          apply Z2Nat.inj_le; lia. }
        lia. }
      assert (Z.to_nat (h - cap) ≤ p)%nat as Hle2.
      { unfold p. 
        assert (Z.to_nat h = (Z.to_nat (h - cap) + Z.to_nat cap)%nat) as Hsum.
        { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
        assert (1 ≤ Z.to_nat cap)%nat as Hone.
        { replace 1%nat with (Z.to_nat 1%Z) by reflexivity.
          apply Z2Nat.inj_le; lia. }
        lia. }
      assert (fuel < S fuel)%nat as Hsmall by lia.
      assert (p < S fuel)%nat as Hsmall2 by (unfold p; lia).
      rewrite (IH fuel Hsmall (h - cap)%Z Hnn' Hle1).
      rewrite (IH p Hsmall2 (h - cap)%Z Hnn' Hle2).
      reflexivity.
    + destruct (Z.to_nat h) as [|n] eqn:Hn.
      * reflexivity.
      * simpl. destruct (decide (cap ≤ h)%Z); [lia|]. reflexivity.
Qed.

Lemma bring_nonneg_step h cap :
  (0 < cap)%Z → (h < 0)%Z →
  bring_nonneg (Z.to_nat (Z.max 0 (- h))) h cap =
    bring_nonneg (Z.to_nat (Z.max 0 (- (h + cap)))) (h + cap) cap.
Proof.
  intros Hcap Hn.
  assert (Z.max 0 (- h) = - h)%Z as -> by (rewrite Z.max_r; lia).
  assert (0 < Z.to_nat (- h))%nat as Hpos.
  { apply Nat.neq_0_lt_0. intros Hz. apply z_to_nat_0 in Hz. lia. }
  set (p := Nat.pred (Z.to_nat (- h))).
  assert (Z.to_nat (- h) = S p) as -> by (unfold p; lia).
  simpl. destruct (decide (h < 0)%Z); [|lia].
  rewrite (bring_nonneg_ge (h + cap)%Z cap p Hcap).
  { reflexivity. }
  unfold p.
  destruct (Z_lt_le_dec (h + cap) 0) as [Hstill|Hdone].
  - assert (Z.max 0 (- (h + cap)) = (- h - cap))%Z as -> by (rewrite Z.max_r; lia).
    assert (Z.to_nat (- h) = (Z.to_nat (- h - cap) + Z.to_nat cap)%nat) as Hsum.
    { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
    assert (1 ≤ Z.to_nat cap)%nat as Hone.
    { replace 1%nat with (Z.to_nat 1%Z) by reflexivity. apply Z2Nat.inj_le; lia. }
    lia.
  - assert (Z.max 0 (- (h + cap)) = 0)%Z as -> by (rewrite Z.max_l; lia). lia.
Qed.

Lemma bring_below_finished h cap :
  (0 ≤ h)%Z → (h < cap)%Z →
  bring_below (Z.to_nat h) h cap = h.
Proof.
  intros H0 Hlt.
  destruct (Z.to_nat h) as [|n]; simpl.
  - reflexivity.
  - destruct (decide (cap ≤ h)%Z); [lia|reflexivity].
Qed.

Lemma bring_below_step h cap :
  (0 < cap)%Z → (0 ≤ h)%Z → (cap ≤ h)%Z →
  bring_below (Z.to_nat h) h cap =
    bring_below (Z.to_nat (h - cap)) (h - cap) cap.
Proof.
  intros Hcap Hnn Hge.
  assert (0 < Z.to_nat h)%nat as Hpos.
  { apply Nat.neq_0_lt_0. intros Hz. apply z_to_nat_0 in Hz. lia. }
  set (p := Nat.pred (Z.to_nat h)).
  assert (Z.to_nat h = S p) as -> by (unfold p; lia).
  simpl. destruct (decide (cap ≤ h)%Z); [|lia].
  rewrite (bring_below_ge (h - cap)%Z cap p Hcap).
  { reflexivity. }
  { lia. }
  unfold p.
  assert (Z.to_nat h = (Z.to_nat (h - cap) + Z.to_nat cap)%nat) as Hsum.
  { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
  assert (1 ≤ Z.to_nat cap)%nat as Hone.
  { replace 1%nat with (Z.to_nat 1%Z) by reflexivity. apply Z2Nat.inj_le; lia. }
  lia.
Qed.

Lemma residue_spec k cap :
  (0 < cap)%Z →
  (0 ≤ residue k cap < cap)%Z ∧ residue k cap = Z.modulo k cap.
Proof.
  intros Hcap. unfold residue. cbv beta zeta.
  set (h := bring_nonneg (Z.to_nat (Z.max 0 (- k))) k cap).
  assert ((0 ≤ h)%Z ∧ Z.modulo h cap = Z.modulo k cap) as [Hnn Hmod].
  { unfold h. apply bring_nonneg_spec; [done|lia]. }
  destruct (bring_below_spec h cap (Z.to_nat h)) as [Hrng Hmod']; [done|done|lia|].
  split; [done|].
  rewrite <- (Z.mod_small (bring_below (Z.to_nat h) h cap) cap Hrng).
  rewrite Hmod'. rewrite Hmod. done.
Qed.

Lemma pow_positive e : (0 < 2 ^ e)%nat.
Proof. induction e; simpl; lia. Qed.

Lemma residue_nat_lt k cap :
  (0 < cap)%nat → (Z.to_nat (residue k (Z.of_nat cap)) < cap)%nat.
Proof.
  intros Hcap.
  destruct (residue_spec k (Z.of_nat cap)) as [Hrng Heq].
  { lia. }
  apply Nat2Z.inj_lt. rewrite Z2Nat.id; [|lia]. lia.
Qed.

(** [bucket] is that remainder, as an index. For a power-of-two capacity it
is the mask the source computes with [capacity - 1]. *)

Definition bucket (k : Z) (cap : nat) : nat :=
  Z.to_nat (residue k (Z.of_nat cap)).

Lemma bucket_lt k cap : (0 < cap)%nat → (bucket k cap < cap)%nat.
Proof. apply residue_nat_lt. Qed.

Definition probe_slot (start step cap : nat) : nat :=
  ((start + step) `mod` cap)%nat.

Lemma probe_slot_lt start step cap :
  (0 < cap)%nat → (probe_slot start step cap < cap)%nat.
Proof. intros. apply Nat.mod_upper_bound. lia. Qed.

Lemma probe_slot_sub start step cap :
  (0 < cap)%nat → (start < cap)%nat → (step < cap)%nat →
  probe_slot start step cap =
    (if decide ((start + step) < cap)%nat then start + step
     else start + step - cap)%nat.
Proof.
  intros Hcap Hs Hstep. unfold probe_slot.
  destruct (decide ((start + step) < cap)%nat) as [Hlt|Hge].
  - apply Nat.mod_small. done.
  - set (r := (start + step - cap)%nat).
    assert ((start + step) = r + cap)%nat as ->.
    { unfold r. lia. }
    rewrite (Nat.add_comm r cap).
    replace (cap + r)%nat with (r + cap)%nat by lia.
    replace cap with (1 * cap)%nat at 1 by lia.
    rewrite Nat.Div0.mod_add.
    apply Nat.mod_small. unfold r. lia.
Qed.

Definition steps_between (b i cap : nat) : nat :=
  (if decide (b ≤ i)%nat then i - b else i + cap - b)%nat.

Lemma steps_between_lt b i cap :
  (0 < cap)%nat → (b < cap)%nat → (i < cap)%nat →
  (steps_between b i cap < cap)%nat.
Proof. intros. unfold steps_between. destruct (decide (b ≤ i)%nat); lia. Qed.

Lemma probe_slot_steps b i cap :
  (0 < cap)%nat → (b < cap)%nat → (i < cap)%nat →
  probe_slot b (steps_between b i cap) cap = i.
Proof.
  intros Hcap Hb Hi. unfold steps_between, probe_slot.
  destruct (decide (b ≤ i)%nat) as [Hle|Hgt].
  - replace (b + (i - b))%nat with i by lia. apply Nat.mod_small. lia.
  - replace (b + (i + cap - b))%nat with (i + 1 * cap)%nat by lia.
    rewrite Nat.Div0.mod_add. apply Nat.mod_small. lia.
Qed.

Lemma probe_slot_inj start cap s1 s2 :
  (0 < cap)%nat → (start < cap)%nat → (s1 < cap)%nat → (s2 < cap)%nat →
  probe_slot start s1 cap = probe_slot start s2 cap → s1 = s2.
Proof.
  intros Hcap Hs Hs1 Hs2 Heq.
  rewrite probe_slot_sub in Heq; [|done|done|done].
  rewrite probe_slot_sub in Heq; [|done|done|done].
  destruct (decide ((start + s1) < cap)%nat);
    destruct (decide ((start + s2) < cap)%nat); lia.
Qed.

Lemma steps_of_slot start d cap :
  (0 < cap)%nat → (start < cap)%nat → (d < cap)%nat →
  steps_between start (probe_slot start d cap) cap = d.
Proof.
  intros Hcap Hs Hd.
  assert (probe_slot start d cap < cap)%nat as Hslot.
  { apply probe_slot_lt. done. }
  apply (probe_slot_inj start cap (steps_between start (probe_slot start d cap) cap) d);
    [done|done| |done|].
  - apply steps_between_lt; [done|done|done].
  - rewrite (probe_slot_steps start _ cap Hcap Hs Hslot). done.
Qed.

(** * The map carried by the three columns *)

Fixpoint contents_of (tags keys vals : list Z) : gmap Z Z :=
  match tags, keys, vals with
  | t :: tags, k :: keys, v :: vals =>
      let m := contents_of tags keys vals in
      if decide (t = tag_occ) then <[k := v]> m else m
  | _, _, _ => ∅
  end.

Fixpoint occ_keys (tags keys : list Z) : list Z :=
  match tags, keys with
  | t :: tags, k :: keys =>
      if decide (t = tag_occ) then k :: occ_keys tags keys else occ_keys tags keys
  | _, _ => []
  end.

Fixpoint count_occ (tags : list Z) : nat :=
  match tags with
  | [] => 0
  | t :: tags =>
      (if decide (t = tag_occ) then 1 else 0) + count_occ tags
  end.

Lemma occ_in tags keys i k :
  tags !! i = Some tag_occ → keys !! i = Some k → k ∈ occ_keys tags keys.
Proof.
  revert tags keys. induction i as [|i IH]; intros tags keys Ht Hk.
  - destruct tags as [|t tags]; [discriminate|].
    destruct keys as [|k0 keys]; [discriminate|].
    simpl in Ht, Hk. simplify_eq. simpl. destruct (decide (tag_occ = tag_occ)); [|congruence].
    apply elem_of_cons. by left.
  - destruct tags as [|t tags]; [discriminate|].
    destruct keys as [|k0 keys]; [discriminate|].
    simpl in Ht, Hk. simpl. destruct (decide (t = tag_occ)).
    + apply elem_of_cons. right. by eapply IH.
    + by eapply IH.
Qed.

Lemma occ_unique tags keys i j k :
  NoDup (occ_keys tags keys) →
  tags !! i = Some tag_occ → keys !! i = Some k →
  tags !! j = Some tag_occ → keys !! j = Some k →
  i = j.
Proof.
  revert keys i j. induction tags as [|t tags IH]; intros keys i j Hdup Hi Hk Hj Hkj.
  - discriminate.
  - destruct keys as [|k0 keys]; [discriminate|].
    simpl in Hi, Hk, Hj, Hkj, Hdup.
    destruct (decide (t = tag_occ)) as [Ht|Ht].
    + apply NoDup_cons in Hdup as [Hnin Hdup].
      destruct i as [|i]; destruct j as [|j].
      * reflexivity.
      * simpl in Hi, Hk, Hj, Hkj. simplify_eq.
        exfalso. apply Hnin. eapply occ_in; eauto.
      * simpl in Hi, Hk, Hj, Hkj. simplify_eq.
        exfalso. apply Hnin. eapply occ_in; eauto.
      * simpl in Hi, Hk, Hj, Hkj. f_equal. eapply IH; eauto.
    + destruct i as [|i]; destruct j as [|j].
      * simpl in *. congruence.
      * simpl in *. congruence.
      * simpl in *. congruence.
      * simpl in *. f_equal. eapply IH; eauto.
Qed.

Lemma contents_none_iff tags keys vals k :
  length keys = length tags → length vals = length tags →
  contents_of tags keys vals !! k = None ↔ k ∉ occ_keys tags keys.
Proof.
  revert keys vals. induction tags as [|t tags IH]; intros keys vals Hlk Hlv.
  - destruct keys, vals; simpl in *; try discriminate.
    split; [intros _; by apply not_elem_of_nil|done].
  - destruct keys as [|k0 keys]; [simpl in Hlk; discriminate|].
    destruct vals as [|v0 vals]; [simpl in Hlv; discriminate|].
    simpl in Hlk, Hlv. injection Hlk as Hlk. injection Hlv as Hlv.
    simpl. destruct (decide (t = tag_occ)) as [Ht|Ht].
    + split.
      * intros Hnone Hin. apply elem_of_cons in Hin as [->|Hin].
        -- rewrite lookup_insert in Hnone. discriminate.
        -- assert (k0 ≠ k) as Hne.
           { intros ->. rewrite lookup_insert in Hnone. discriminate. }
           rewrite lookup_insert_ne in Hnone; [|exact Hne].
           apply (proj1 (IH keys vals Hlk Hlv)) in Hnone.
           by apply Hnone.
      * intros Hnin. apply not_elem_of_cons in Hnin as [Hne Hnin].
        rewrite lookup_insert_ne; [|done]. by eapply IH.
    + by apply IH.
Qed.

Lemma contents_at tags keys vals i k v :
  length keys = length tags → length vals = length tags →
  NoDup (occ_keys tags keys) →
  tags !! i = Some tag_occ → keys !! i = Some k → vals !! i = Some v →
  contents_of tags keys vals !! k = Some v.
Proof.
  intros Hlk Hlv Hdup Ht Hk Hv.
  revert keys vals i k v Hlk Hlv Hdup Ht Hk Hv.
  induction tags as [|t tags IH]; intros keys vals i k v Hlk Hlv Hdup Ht Hk Hv.
  - discriminate.
  - destruct keys as [|k0 keys]; [simpl in Hlk; discriminate|].
    destruct vals as [|v0 vals]; [simpl in Hlv; discriminate|].
    simpl in Hlk, Hlv. injection Hlk as Hlk. injection Hlv as Hlv.
    simpl in Ht, Hk, Hv, Hdup.
    destruct (decide (t = tag_occ)) as [->|Hnot].
    + simpl in Hdup. apply NoDup_cons in Hdup as [Hnin Hdup].
      destruct i as [|i].
      * simpl in Ht, Hk, Hv. simplify_eq. simpl. by rewrite lookup_insert.
      * simpl in Ht, Hk, Hv.
        assert (k0 ≠ k) as Hne.
        { intros ->. apply Hnin. eapply occ_in; eauto. }
        simpl. rewrite lookup_insert_ne; [|done].
        eapply IH; eauto.
    + simpl. case_decide; [congruence|].
      simpl in Hdup. destruct (decide (t = tag_occ)); [congruence|].
      destruct i as [|i].
      * simpl in Ht. congruence.
      * simpl in Ht, Hk, Hv. eapply IH; eauto.
Qed.

Lemma count_occ_len tags : (count_occ tags ≤ length tags)%nat.
Proof.
  induction tags as [|t tags IH]; simpl; [lia|].
  destruct (decide (t = tag_occ)); lia.
Qed.

Lemma count_insert_fresh tags i :
  tags !! i = Some tag_empty ∨ tags !! i = Some tag_tomb →
  count_occ (<[i := tag_occ]> tags) = S (count_occ tags).
Proof.
  revert tags. induction i as [|i IH]; intros tags Ht.
  - destruct tags as [|t tags]; simpl in Ht.
    + destruct Ht as [Ht|Ht]; discriminate.
    + destruct Ht as [Ht|Ht]; simpl in Ht; inversion Ht; subst; simpl.
      * destruct (decide (tag_occ = tag_occ)); [|congruence].
        destruct (decide (tag_empty = tag_occ)); [unfold tag_empty, tag_occ; lia|].
        lia.
      * destruct (decide (tag_occ = tag_occ)); [|congruence].
        destruct (decide (tag_tomb = tag_occ)); [unfold tag_tomb, tag_occ; lia|].
        lia.
  - destruct tags as [|t tags]; simpl in Ht.
    + destruct Ht as [Ht|Ht]; discriminate.
    + simpl. destruct (decide (t = tag_occ)); rewrite (IH tags Ht); lia.
Qed.

Lemma count_bury tags i :
  tags !! i = Some tag_occ →
  count_occ tags = S (count_occ (<[i := tag_tomb]> tags)).
Proof.
  revert tags. induction i as [|i IH]; intros tags Ht.
  - destruct tags as [|t tags]; simpl in Ht; [discriminate|].
    simpl in Ht. inversion Ht. subst. simpl.
    destruct (decide (tag_occ = tag_occ)); [|congruence].
    destruct (decide (tag_tomb = tag_occ)); [unfold tag_tomb, tag_occ; lia|].
    lia.
  - destruct tags as [|t tags]; simpl in Ht; [discriminate|].
    simpl in Ht. simpl. destruct (decide (t = tag_occ)); rewrite (IH tags Ht); lia.
Qed.

Lemma tags_ok_insert tags i t :
  tags_ok tags → tag_ok t → (i < length tags)%nat →
  tags_ok (<[i := t]> tags).
Proof.
  intros Hok Ht Hi. apply Forall_lookup. intros j u Hu.
  destruct (decide (j = i)) as [->|Hne].
  - rewrite list_lookup_insert in Hu; [|done]. by simplify_eq.
  - rewrite list_lookup_insert_ne in Hu; [|done]. by eapply Forall_lookup_1.
Qed.

Lemma insert_length_eq {A} (i : nat) (x : A) (l : list A) :
  (i < length l)%nat → length (<[i := x]> l) = length l.
Proof. intros. by rewrite length_insert. Qed.

(** * Open addressing

The probe starts at the bucket and walks at most one full turn. The
invariant of the walk is the segment already scanned: the key is absent
there, no empty slot has been passed, and [hole] is the first tombstone
on that segment, if one has been seen. *)

Definition no_empty_before (cap b i : nat) (tags : list Z) : Prop :=
  ∀ j, (j < steps_between b i cap)%nat →
    tags !! probe_slot b j cap ≠ Some tag_empty.

Definition placed (cap : nat) (tags keys : list Z) : Prop :=
  ∀ i k, tags !! i = Some tag_occ → keys !! i = Some k →
    no_empty_before cap (bucket k cap) i tags.

Definition segment_clear (cap start step : nat) (tags keys : list Z) (k : Z) : Prop :=
  ∀ j, (j < step)%nat →
    ∃ t key,
      tags !! probe_slot start j cap = Some t ∧
      keys !! probe_slot start j cap = Some key ∧
      t ≠ tag_empty ∧ (t = tag_occ → key ≠ k).

Fixpoint first_tomb (step start cap : nat) (tags : list Z) : option nat :=
  match step with
  | 0 => None
  | S step =>
      match first_tomb step start cap tags with
      | Some h => Some h
      | None =>
          match tags !! probe_slot start step cap with
          | Some t =>
              if decide (t = tag_tomb) then Some (probe_slot start step cap) else None
          | None => None
          end
      end
  end.

Record probe_prefix (cap start step : nat) (tags keys : list Z)
    (k : Z) (hole : option nat) : Prop := {
  pp_bound : (step ≤ cap)%nat;
  pp_seen : segment_clear cap start step tags keys k;
  pp_hole : hole = first_tomb step start cap tags
}.

Lemma segment_short cap start step d tags keys k :
  (d ≤ step)%nat →
  segment_clear cap start step tags keys k →
  segment_clear cap start d tags keys k.
Proof. intros Hle Hseen j Hj. apply Hseen. lia. Qed.

Lemma segment_no_empty cap start d tags keys k :
  (0 < cap)%nat → (start < cap)%nat → (d < cap)%nat →
  segment_clear cap start d tags keys k →
  no_empty_before cap start (probe_slot start d cap) tags.
Proof.
  intros Hcap Hs Hd Hseen j Hj.
  rewrite steps_of_slot in Hj; [|done|done|done].
  destruct (Hseen j Hj) as (t & key & Ht & _ & Hne & _).
  intros Heq. rewrite Ht in Heq. inversion Heq. contradiction.
Qed.

Lemma prefix_zero cap start tags keys k :
  (start ≤ cap)%nat →
  probe_prefix cap start 0 tags keys k None.
Proof. intros. constructor; [lia| |reflexivity]. intros j Hj. lia. Qed.

Lemma prefix_pred cap start step tags keys k hole :
  probe_prefix cap start (S step) tags keys k hole →
  probe_prefix cap start step tags keys k (first_tomb step start cap tags).
Proof.
  intros [Hbound Hseen Hhole]. constructor.
  - lia.
  - intros j Hj. apply Hseen. lia.
  - reflexivity.
Qed.

Lemma first_tomb_S step start cap tags :
  first_tomb (S step) start cap tags =
    match first_tomb step start cap tags with
    | Some h => Some h
    | None =>
        match tags !! probe_slot start step cap with
        | Some t =>
            if decide (t = tag_tomb) then Some (probe_slot start step cap) else None
        | None => None
        end
    end.
Proof. reflexivity. Qed.

Lemma first_tomb_none_clear step start cap tags :
  (0 < cap)%nat → (start < cap)%nat → (step ≤ cap)%nat →
  first_tomb step start cap tags = None →
  ∀ j, (j < step)%nat → tags !! probe_slot start j cap ≠ Some tag_tomb.
Proof.
  revert start. induction step as [|step IH]; intros start Hcap Hs Hle Hnone j Hj.
  - lia.
  - simpl in Hnone. destruct (first_tomb step start cap tags) as [h|] eqn:Hf.
    + discriminate.
    + intros Heq.
      destruct (decide (j = step)) as [->|Hne].
      * rewrite Heq in Hnone.
        destruct (decide (tag_tomb = tag_tomb)); congruence.
      * apply (IH start Hcap Hs ltac:(lia) Hf j ltac:(lia) Heq).
Qed.

Lemma first_tomb_some step start cap tags h :
  (0 < cap)%nat → (start < cap)%nat → (step ≤ cap)%nat →
  first_tomb step start cap tags = Some h →
  ∃ d, (d < step)%nat ∧ h = probe_slot start d cap ∧ tags !! h = Some tag_tomb.
Proof.
  intros Hcap Hs Hle Hf.
  remember step as n eqn:Hn in |- *.
  revert step h Hn Hle Hf.
  induction n as [|n IH]; intros step h Hn Hle Hf.
  - subst step. discriminate.
  - subst step. cbn [first_tomb] in Hf.
    destruct (first_tomb n start cap tags) as [h'|] eqn:Hprev.
    + simpl in Hf. injection Hf as <-.
      destruct (IH n h' eq_refl ltac:(lia) Hprev) as (d & Hd & -> & Htag).
      exists d. split; [lia|]. split; done.
    + destruct (tags !! probe_slot start n cap) as [t|] eqn:Ht; [|discriminate].
      destruct (decide (t = tag_tomb)) as [->|]; [|discriminate].
      simpl in Hf. injection Hf as <-. exists n.
      split; [lia|]. split; [done|]. rewrite Ht. done.
Qed.

Lemma count_lt_exists tags :
  (count_occ tags < length tags)%nat →
  ∃ i t, tags !! i = Some t ∧ t ≠ tag_occ.
Proof.
  induction tags as [|t tags IH]; simpl; [lia|].
  destruct (decide (t = tag_occ)) as [->|Hne].
  - intros Hlt. destruct IH as (i & u & Hi & Hu); [lia|].
    exists (S i), u. split; done.
  - intros _. exists 0%nat, t. split; [done|done].
Qed.

Inductive probe_out :=
  | PFound (idx : nat) (pval : Z)
  | PAbsent (idx : nat).

Definition hole_or (hole : option nat) (s : nat) : nat :=
  match hole with Some h => h | None => s end.

Fixpoint probe_from (n start step cap : nat) (tags keys vals : list Z)
    (k : Z) (hole : option nat) : probe_out :=
  match n with
  | 0 => PAbsent (hole_or hole start)
  | S n =>
      let s := probe_slot start step cap in
      match tags !! s with
      | None => PAbsent (hole_or hole s)
      | Some t =>
          if decide (t = tag_empty) then PAbsent (hole_or hole s)
          else if decide (t = tag_occ) then
            match keys !! s, vals !! s with
            | Some key, Some v =>
                if decide (key = k) then PFound s v
                else probe_from n start (S step) cap tags keys vals k hole
            | _, _ => PAbsent (hole_or hole s)
            end
          else
            let hole' := match hole with None => Some s | Some _ => hole end in
            probe_from n start (S step) cap tags keys vals k hole'
      end
  end.

Definition probe (cap start : nat) (tags keys vals : list Z) (k : Z) : probe_out :=
  probe_from cap start 0 cap tags keys vals k None.

Definition cell_clear (cap start step : nat) (tags keys : list Z) (k : Z) : Prop :=
  ∃ t key,
    tags !! probe_slot start step cap = Some t ∧
    keys !! probe_slot start step cap = Some key ∧
    t ≠ tag_empty ∧ (t = tag_occ → key ≠ k).

Lemma seen_here cap start step tags keys k :
  segment_clear cap start (S step) tags keys k →
  cell_clear cap start step tags keys k.
Proof. intros H. apply H. lia. Qed.

Lemma scan_skip d cap start tags keys vals k :
  (0 < cap)%nat → (start < cap)%nat → (d ≤ cap)%nat →
  length tags = cap → length keys = cap → length vals = cap →
  tags_ok tags →
  probe_prefix cap start d tags keys k (first_tomb d start cap tags) →
  probe_from cap start 0 cap tags keys vals k None =
    probe_from (cap - d) start d cap tags keys vals k
      (first_tomb d start cap tags).
Proof.
  intros Hcap Hs Hd Hltag Hlkey Hlval Hok Hpre.
  induction d as [|d IH] in Hd, Hpre |- *.
  - replace (cap - 0)%nat with cap by lia. simpl. reflexivity.
  - assert (d ≤ cap)%nat as Hd' by lia.
    destruct Hpre as [Hbound Hseen Hhole].
    assert (probe_prefix cap start d tags keys k (first_tomb d start cap tags)) as Hpre'.
    { constructor; [lia| |reflexivity]. intros j Hj. apply Hseen. lia. }
    specialize (IH Hd' Hpre').
    assert (probe_from cap start 0 cap tags keys vals k None =
            probe_from (cap - d) start d cap tags keys vals k
              (first_tomb d start cap tags)) as Hstep.
    { exact IH. }
    assert ((cap - d) = S (cap - S d))%nat as Hfuel by lia.
    rewrite Hstep. rewrite Hfuel.
    destruct (seen_here cap start d tags keys k) as (t & key & Ht & Hk & Hne & Hkey).
    { exact Hseen. }
    simpl. rewrite Ht.
    destruct (decide (t = tag_empty)) as [He|Hne'].
    { contradiction. }
    destruct (decide (t = tag_occ)) as [Hocc|Hnot].
    + rewrite Hk. 
      destruct (vals !! probe_slot start d cap) as [v|] eqn:Hv.
      * destruct (decide (key = k)) as [Hk'|Hnk].
        -- exfalso. apply Hkey; [exact Hocc|exact Hk'].
        -- destruct (first_tomb d start cap tags) as [h|]; [reflexivity|].
           destruct (decide (t = tag_tomb)) as [Htomb|].
           ++ exfalso. rewrite Htomb in Hocc.
              unfold tag_occ, tag_tomb in Hocc. congruence.
           ++ reflexivity.
      * exfalso.
        assert (is_Some (vals !! probe_slot start d cap)) as [v Hv'].
        { apply lookup_lt_is_Some_2. rewrite Hlval. apply probe_slot_lt. done. }
        rewrite Hv in Hv'. discriminate.
    + assert (t = tag_tomb) as Htomb.
      { destruct (tags_ok_lookup tags (probe_slot start d cap) t Hok Ht)
          as [H0|[H1|H2]]; [contradiction|contradiction|exact H2]. }
      rewrite Htomb.
      destruct (first_tomb d start cap tags) as [h|]; [reflexivity|].
      destruct (decide (tag_tomb = tag_tomb)); [|congruence].
      reflexivity.
Qed.

Lemma probe_hit_now cap start d tags keys vals k v hole :
  (0 < cap)%nat → (start < cap)%nat → (d < cap)%nat →
  tags !! probe_slot start d cap = Some tag_occ →
  keys !! probe_slot start d cap = Some k →
  vals !! probe_slot start d cap = Some v →
  probe_from (cap - d) start d cap tags keys vals k hole = PFound (probe_slot start d cap) v.
Proof.
  intros Hcap Hs Hd Ht Hk Hv.
  assert ((cap - d) = S (cap - S d))%nat as -> by lia.
  simpl. rewrite Ht. rewrite Hk. rewrite Hv.
  destruct (decide (tag_occ = tag_empty)) as [Hbad|].
  { unfold tag_occ, tag_empty in Hbad. congruence. }
  destruct (decide (tag_occ = tag_occ)) as [|Hbad]; [|exfalso; apply Hbad; reflexivity].
  destruct (decide (k = k)) as [|Hbad']; [|exfalso; apply Hbad'; reflexivity].
  reflexivity.
Qed.

Lemma placed_clear cap tags keys i k :
  (0 < cap)%nat → (i < cap)%nat →
  length tags = cap → length keys = cap →
  NoDup (occ_keys tags keys) →
  placed cap tags keys →
  tags !! i = Some tag_occ → keys !! i = Some k →
  let b := bucket k cap in
  let d := steps_between b i cap in
  segment_clear cap b d tags keys k.
Proof.
  intros Hcap Hi Hltag Hlkey Hdup Hplace Ht Hk b d j Hj.
  assert (b < cap)%nat as Hb by (apply bucket_lt; done).
  assert (d < cap)%nat as Hd by (apply steps_between_lt; done).
  assert (j < cap)%nat as Hjcap by lia.
  set (s := probe_slot b j cap).
  destruct (lookup_lt_is_Some_2 tags s) as [t Hts].
  { rewrite Hltag. apply probe_slot_lt. done. }
  destruct (lookup_lt_is_Some_2 keys s) as [key Hks].
  { rewrite Hlkey. apply probe_slot_lt. done. }
  exists t, key. do 2 (split; [done|]).
  assert (t ≠ tag_empty) as Hne.
  { intros ->.
    apply (Hplace i k Ht Hk j).
    { unfold d in Hj. exact Hj. }
    { unfold s. done. } }
  split; [exact Hne|].
  intros Hocc ->.
  assert (s ≠ i) as Hsne.
  { intros Heq. unfold s in Heq.
    assert (probe_slot b d cap = i) as Hid.
    { unfold d. apply probe_slot_steps; done. }
    assert (j = d) as Hjd.
    { apply (probe_slot_inj b cap j d); [done|exact Hb|exact Hjcap|exact Hd|].
      rewrite Heq. rewrite Hid. reflexivity. }
    lia. }
  exfalso.
  assert (s = i) as Heqsi.
  { apply (occ_unique tags keys s i k Hdup).
    - rewrite Hocc in Hts. exact Hts.
    - exact Hks.
    - exact Ht.
    - exact Hk. }
  apply Hsne. exact Heqsi.
Qed.

Lemma probe_found cap tags keys vals i k v :
  (0 < cap)%nat → (i < cap)%nat →
  length tags = cap → length keys = cap → length vals = cap →
  tags_ok tags → NoDup (occ_keys tags keys) → placed cap tags keys →
  tags !! i = Some tag_occ → keys !! i = Some k → vals !! i = Some v →
  probe cap (bucket k cap) tags keys vals k = PFound i v.
Proof.
  intros Hcap Hi Hltag Hlkey Hlval Hok Hdup Hplace Ht Hk Hv.
  set (b := bucket k cap).
  set (d := steps_between b i cap).
  assert (b < cap)%nat as Hb by (unfold b; apply bucket_lt; done).
  assert (d < cap)%nat as Hd by (unfold d; apply steps_between_lt; done).
  assert (probe_slot b d cap = i) as Hslot.
  { unfold d. apply probe_slot_steps; done. }
  assert (segment_clear cap b d tags keys k) as Hseen.
  { eapply placed_clear; eauto. }
  assert (probe_prefix cap b d tags keys k (first_tomb d b cap tags)) as Hpre.
  { constructor; [lia|exact Hseen|reflexivity]. }
  unfold probe.
  rewrite (scan_skip d cap b tags keys vals k Hcap Hb ltac:(lia)
             Hltag Hlkey Hlval Hok Hpre).
  rewrite <- Hslot.
  apply probe_hit_now; try done.
  - rewrite Hslot. exact Ht.
  - rewrite Hslot. exact Hk.
  - rewrite Hslot. exact Hv.
Qed.

Lemma full_scan_hole cap start tags keys k hole :
  (0 < cap)%nat → (start < cap)%nat →
  length tags = cap → tags_ok tags →
  (count_occ tags < cap)%nat →
  probe_prefix cap start cap tags keys k hole →
  ∃ h, hole = Some h ∧ (h < cap)%nat ∧ tags !! h = Some tag_tomb ∧
       no_empty_before cap start h tags.
Proof.
  intros Hcap Hs Hlen Hok Hcount [Hbound Hseen Hhole].
  destruct (first_tomb cap start cap tags) as [h|] eqn:Hf.
  - destruct (first_tomb_some cap start cap tags h Hcap Hs ltac:(lia) Hf)
      as (d & Hd & -> & Htag).
    exists (probe_slot start d cap).
    split; [rewrite Hhole; done|].
    split; [apply probe_slot_lt; done|].
    split; [exact Htag|].
    apply (segment_no_empty cap start d tags keys k); [done|done|lia|].
    apply (segment_short cap start cap d tags keys k); [lia|exact Hseen].
  - exfalso.
    assert (count_occ tags < length tags)%nat as Hclen by (rewrite Hlen; exact Hcount).
    destruct (count_lt_exists tags Hclen) as (i & t & Hi & Hne).
    assert (i < cap)%nat as Hicap.
    { apply lookup_lt_Some in Hi. lia. }
    set (j := steps_between start i cap).
    assert (probe_slot start j cap = i) as Hslot.
    { unfold j. apply probe_slot_steps; done. }
    assert (j < cap)%nat as Hj by (unfold j; apply steps_between_lt; done).
    destruct (Hseen j Hj) as (t' & key & Ht' & _ & Hempty & _).
    rewrite Hslot in Ht'. rewrite Hi in Ht'.
    assert (t' = t) as -> by congruence.
    assert (t = tag_tomb) as Htomb.
    { destruct (tags_ok_lookup tags i t Hok Hi) as [H0|[H1|H2]];
        [contradiction|contradiction|exact H2]. }
    assert (tags !! probe_slot start j cap ≠ Some tag_tomb) as Hnt.
    { apply (first_tomb_none_clear cap start cap tags Hcap Hs ltac:(lia) Hf j Hj). }
    rewrite Hslot in Hnt. rewrite Hi in Hnt. rewrite Htomb in Hnt.
    apply Hnt. reflexivity.
Qed.

Lemma probe_from_inv n start step cap tags keys vals k hole :
  (0 < cap)%nat → (start < cap)%nat →
  (step + n = cap)%nat →
  length tags = cap → length keys = cap → length vals = cap →
  tags_ok tags → (count_occ tags < cap)%nat →
  probe_prefix cap start step tags keys k hole →
  match probe_from n start step cap tags keys vals k hole with
  | PFound idx v =>
      (idx < cap)%nat ∧ tags !! idx = Some tag_occ ∧
      keys !! idx = Some k ∧ vals !! idx = Some v ∧
      no_empty_before cap start idx tags
  | PAbsent idx =>
      (idx < cap)%nat ∧
      (tags !! idx = Some tag_empty ∨ tags !! idx = Some tag_tomb) ∧
      no_empty_before cap start idx tags
  end.
Proof.
  intros Hcap Hs Hsum Hltag Hlkey Hlval Hok Hcount Hpre.
  remember n as fuel eqn:Hfuel in |- *.
  revert n step hole Hfuel Hsum Hpre.
  induction fuel as [|fuel IH]; intros n step hole Hfuel Hsum Hpre.
  - subst n. assert (step = cap) as -> by lia. simpl.
    destruct (full_scan_hole cap start tags keys k hole) as (h & -> & Hh & Htag & Hpath);
      try done.
    simpl. split; [exact Hh|]. split; [by right|exact Hpath].
  - subst n. destruct Hpre as [Hbound Hseen Hhole].
    assert (step < cap)%nat as Hstep by lia.
    set (s := probe_slot start step cap).
    assert (s < cap)%nat as Hs' by (unfold s; apply probe_slot_lt; done).
    destruct (lookup_lt_is_Some_2 tags s) as [t Ht].
    { rewrite Hltag. exact Hs'. }
    destruct (lookup_lt_is_Some_2 keys s) as [key Hk].
    { rewrite Hlkey. exact Hs'. }
    destruct (lookup_lt_is_Some_2 vals s) as [v Hv].
    { rewrite Hlval. exact Hs'. }
    cbn [probe_from]. unfold s. rewrite Ht.
    destruct (decide (t = tag_empty)) as [->|Hne].
    + simpl. split.
      * destruct hole as [h|]; [|exact Hs'].
        assert (first_tomb step start cap tags = Some h) as Hf by (rewrite <- Hhole; reflexivity).
        destruct (first_tomb_some step start cap tags h Hcap Hs ltac:(lia) Hf)
          as (d & Hd & -> & _).
        apply probe_slot_lt; done.
      * split.
        -- destruct hole as [h|]; [right|by left].
           assert (first_tomb step start cap tags = Some h) as Hf by (rewrite <- Hhole; reflexivity).
           destruct (first_tomb_some step start cap tags h Hcap Hs ltac:(lia) Hf)
             as (d & Hd & -> & Htag). exact Htag.
        -- destruct hole as [h|].
           ++ assert (first_tomb step start cap tags = Some h) as Hf by (rewrite <- Hhole; reflexivity).
              destruct (first_tomb_some step start cap tags h Hcap Hs ltac:(lia) Hf)
                as (d & Hd & -> & _).
              apply (segment_no_empty cap start d tags keys k); [done|done|lia|].
              apply (segment_short cap start step d tags keys k); [lia|exact Hseen].
           ++ apply (segment_no_empty cap start step tags keys k); [done|done|exact Hstep|exact Hseen].
    + destruct (decide (t = tag_occ)) as [->|Hnot].
      * rewrite Hk. rewrite Hv.
        destruct (decide (key = k)) as [->|Hnk].
        -- simpl. split; [exact Hs'|].
           split; [exact Ht|]. split; [exact Hk|]. split; [exact Hv|].
           apply (segment_no_empty cap start step tags keys k); [done|done|exact Hstep|exact Hseen].
        -- assert ((S step + fuel = cap)%nat) as Hsum' by lia.
           assert (probe_prefix cap start (S step) tags keys k hole) as Hpre'.
           { constructor; [lia| |].
             - intros j Hj. destruct (decide (j = step)) as [->|Hjne].
               + exists tag_occ, key. unfold s in Ht, Hk.
                 split; [exact Ht|]. split; [exact Hk|].
                 split; [exact Hne|]. intros _. exact Hnk.
               + apply Hseen. lia.
             - rewrite Hhole. rewrite first_tomb_S. unfold s in Ht. rewrite Ht.
               destruct (first_tomb step start cap tags); [reflexivity|].
               destruct (decide (tag_occ = tag_tomb)) as [Hbad|].
               { exfalso. unfold tag_occ, tag_tomb in Hbad. discriminate. }
               reflexivity. }
           apply (IH fuel (S step) hole eq_refl Hsum' Hpre').
      * assert (t = tag_tomb) as Htomb.
        { destruct (tags_ok_lookup tags s t Hok Ht) as [H0|[H1|H2]];
            [contradiction|contradiction|exact H2]. }
        set (hole' := match hole with None => Some s | Some _ => hole end).
        assert ((S step + fuel = cap)%nat) as Hsum' by lia.
        assert (probe_prefix cap start (S step) tags keys k hole') as Hpre'.
        { constructor; [lia| |].
          - intros j Hj. destruct (decide (j = step)) as [->|Hjne].
            + exists t, key. unfold s in Ht, Hk.
              split; [exact Ht|]. split; [exact Hk|].
              split; [exact Hne|]. intros Hocc. rewrite Htomb in Hocc.
              unfold tag_tomb, tag_occ in Hocc. congruence.
            + apply Hseen. lia.
          - unfold hole'. rewrite Hhole. rewrite first_tomb_S.
            unfold s in Ht. rewrite Ht. rewrite Htomb.
            destruct (decide (tag_tomb = tag_tomb)); [|congruence].
            destruct (first_tomb step start cap tags); reflexivity. }
        apply (IH fuel (S step) hole' eq_refl Hsum' Hpre').
Qed.

Lemma occ_index tags keys k :
  k ∈ occ_keys tags keys →
  ∃ i, tags !! i = Some tag_occ ∧ keys !! i = Some k.
Proof.
  revert keys. induction tags as [|t tags IH]; intros keys Hin.
  - destruct keys; simpl in Hin; exfalso; eapply not_elem_of_nil; exact Hin.
  - destruct keys as [|k0 keys].
    + simpl in Hin. exfalso. eapply not_elem_of_nil. exact Hin.
    + simpl in Hin. destruct (decide (t = tag_occ)) as [->|Hnot].
      * apply elem_of_cons in Hin as [->|Hin].
        -- exists 0%nat. simpl. split; reflexivity.
        -- destruct (IH keys Hin) as (i & Ht & Hk). exists (S i). split; done.
      * destruct (IH keys Hin) as (i & Ht & Hk). exists (S i). split; done.
Qed.

Lemma probe_shape cap tags keys vals k :
  (0 < cap)%nat →
  length tags = cap → length keys = cap → length vals = cap →
  tags_ok tags → NoDup (occ_keys tags keys) → placed cap tags keys →
  (count_occ tags < cap)%nat →
  match probe cap (bucket k cap) tags keys vals k with
  | PFound idx v => contents_of tags keys vals !! k = Some v
  | PAbsent idx =>
      (idx < cap)%nat ∧
      (tags !! idx = Some tag_empty ∨ tags !! idx = Some tag_tomb) ∧
      no_empty_before cap (bucket k cap) idx tags ∧
      contents_of tags keys vals !! k = None
  end.
Proof.
  intros Hcap Hltag Hlkey Hlval Hok Hdup Hplace Hcount.
  set (b := bucket k cap).
  assert (b < cap)%nat as Hb by (unfold b; apply bucket_lt; done).
  assert (probe_prefix cap b 0 tags keys k None) as Hpre.
  { apply prefix_zero. lia. }
  pose proof (probe_from_inv cap b 0 cap tags keys vals k None Hcap Hb
                ltac:(lia) Hltag Hlkey Hlval Hok Hcount Hpre) as Hinv.
  unfold probe.
  destruct (probe_from cap b 0 cap tags keys vals k None)
    as [idx v|idx] eqn:Hr.
  - destruct Hinv as (Hidx & Ht & Hk & Hv & _).
    apply (contents_at tags keys vals idx k v).
    { rewrite Hlkey. rewrite Hltag. reflexivity. }
    { rewrite Hlval. rewrite Hltag. reflexivity. }
    { exact Hdup. }
    { exact Ht. }
    { exact Hk. }
    { exact Hv. }
  - destruct Hinv as (Hidx & Htag & Hpath).
    split; [exact Hidx|]. split; [exact Htag|]. split; [exact Hpath|].
    assert (length keys = length tags) as Hlk.
    { rewrite Hlkey. rewrite Hltag. reflexivity. }
    assert (length vals = length tags) as Hlv.
    { rewrite Hlval. rewrite Hltag. reflexivity. }
    apply (contents_none_iff tags keys vals k Hlk Hlv).
    intros Hin.
    destruct (occ_index tags keys k Hin) as (i & Ht & Hk).
    assert (i < cap)%nat as Hi.
    { apply lookup_lt_Some in Ht. lia. }
    destruct (lookup_lt_is_Some_2 vals i) as [v Hv].
    { rewrite Hlval. exact Hi. }
    assert (probe_from cap b 0 cap tags keys vals k None = PFound i v)
      as Hr'.
    { unfold b. change (probe cap (bucket k cap) tags keys vals k = PFound i v).
      apply probe_found; try done. }
    rewrite Hr in Hr'. discriminate.
Qed.

(** * Insertion, deletion, and growth *)

Lemma tag_occ_ne_empty : tag_occ ≠ tag_empty.
Proof. unfold tag_occ, tag_empty. lia. Qed.

Lemma tag_tomb_ne_empty : tag_tomb ≠ tag_empty.
Proof. unfold tag_tomb, tag_empty. lia. Qed.

Lemma tag_tomb_ne_occ : tag_tomb ≠ tag_occ.
Proof. unfold tag_tomb, tag_occ. lia. Qed.

Lemma twice_add (x : nat) : (x + x = 2 * x)%nat.
Proof. lia. Qed.

Lemma even_pow e : (2 ^ S e = 2 * 2 ^ e)%nat.
Proof. reflexivity. Qed.

Lemma room_for_one cap n :
  (∃ e, cap = (2 ^ S e)%nat) →
  (2 * n < cap)%nat →
  (2 * S n ≤ cap)%nat.
Proof.
  intros [e ->] Hlt.
  rewrite even_pow in Hlt.
  apply Nat.mul_lt_mono_pos_l with (p := 2%nat) in Hlt; [|lia].
  rewrite even_pow.
  apply Nat.mul_le_mono_pos_l; [lia|].
  exact Hlt.
Qed.

Lemma double_pow e : (2 ^ S e + 2 ^ S e = 2 ^ S (S e))%nat.
Proof.
  rewrite twice_add. rewrite <- even_pow. reflexivity.
Qed.

Lemma occ_place_iff tags keys i k k' :
  length keys = length tags →
  (i < length tags)%nat →
  tags !! i ≠ Some tag_occ →
  k' ∈ occ_keys (<[i:=tag_occ]> tags) (<[i:=k]> keys)
  ↔ k' = k ∨ k' ∈ occ_keys tags keys.
Proof.
  revert keys i k k'. induction tags as [|t tags IH]; intros keys i k k' Hlen Hi Hne.
  - simpl in Hi. lia.
  - destruct keys as [|k0 keys]; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    destruct i as [|i].
    + simpl in Hne. simpl.
      destruct (decide (tag_occ = tag_occ)) as [_|Hbad]; [|exfalso; apply Hbad; reflexivity].
      destruct (decide (t = tag_occ)) as [Ht|Ht].
      * exfalso. apply Hne. f_equal. exact Ht.
      * rewrite elem_of_cons. split.
        -- intros [->|Hin]; [by left|by right].
        -- intros [->|Hin]; [by left|by right].
    + simpl in Hi, Hne. simpl.
      destruct (decide (t = tag_occ)) as [->|Hnot].
      * rewrite !elem_of_cons.
        assert (i < length tags)%nat as Hi' by lia.
        pose proof (IH keys i k k' Hlen Hi' Hne) as IH'.
        split.
        -- intros [->|Hin].
           ++ right. by left.
           ++ apply IH' in Hin as [->|Hin]; [by left|right; by right].
        -- intros [->|[->|Hin]].
           ++ right. apply IH'. by left.
           ++ by left.
           ++ right. apply IH'. by right.
      * assert (i < length tags)%nat as Hi' by lia.
        pose proof (IH keys i k k' Hlen Hi' Hne) as IH'.
        exact IH'.
Qed.

Lemma nodup_place tags keys i k :
  length keys = length tags →
  (i < length tags)%nat →
  NoDup (occ_keys tags keys) →
  k ∉ occ_keys tags keys →
  tags !! i ≠ Some tag_occ →
  NoDup (occ_keys (<[i:=tag_occ]> tags) (<[i:=k]> keys)).
Proof.
  revert keys i. induction tags as [|t tags IH]; intros keys i Hlen Hi Hdup Hnin Hne.
  - simpl in Hi. lia.
  - destruct keys as [|k0 keys]; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    destruct i as [|i].
    + simpl in Hne, Hdup, Hnin. simpl.
      destruct (decide (tag_occ = tag_occ)) as [_|Hbad]; [|exfalso; apply Hbad; reflexivity].
      destruct (decide (t = tag_occ)) as [Ht|Ht].
      * exfalso. apply Hne. f_equal. exact Ht.
      * apply NoDup_cons. split; [exact Hnin|exact Hdup].
    + simpl in Hi, Hne, Hdup, Hnin. simpl.
      destruct (decide (t = tag_occ)) as [->|Hnot].
      * simpl in Hdup, Hnin. apply NoDup_cons in Hdup as [Hk0 Hdup].
        apply not_elem_of_cons in Hnin as [Hkk0 Hnin].
        simpl. apply NoDup_cons. split.
        -- intros Hin.
           apply (occ_place_iff tags keys i k k0 Hlen ltac:(lia) Hne) in Hin
             as [Heq|Hin].
           ++ apply Hkk0. symmetry. exact Heq.
           ++ apply Hk0. exact Hin.
        -- apply (IH keys i); [exact Hlen|lia|exact Hdup|exact Hnin|exact Hne].
      * apply (IH keys i); [exact Hlen|lia|exact Hdup|exact Hnin|exact Hne].
Qed.

Lemma contents_place tags keys vals i k v :
  length keys = length tags → length vals = length tags →
  (i < length tags)%nat →
  tags !! i ≠ Some tag_occ →
  k ∉ occ_keys tags keys →
  contents_of (<[i:=tag_occ]> tags) (<[i:=k]> keys) (<[i:=v]> vals) =
  <[k:=v]> (contents_of tags keys vals).
Proof.
  revert keys vals i. induction tags as [|t tags IH]; intros keys vals i Hlk Hlv Hi Hne Hnin.
  - simpl in Hi. lia.
  - destruct keys as [|k0 keys]; [simpl in Hlk; discriminate|].
    destruct vals as [|v0 vals]; [simpl in Hlv; discriminate|].
    simpl in Hlk, Hlv. injection Hlk as Hlk. injection Hlv as Hlv.
    destruct i as [|i].
    + simpl in Hne, Hnin. simpl.
      destruct (decide (tag_occ = tag_occ)) as [_|Hbad]; [|exfalso; apply Hbad; reflexivity].
      destruct (decide (t = tag_occ)) as [Ht|Ht].
      * exfalso. apply Hne. f_equal. exact Ht.
      * reflexivity.
    + simpl in Hi, Hne, Hnin. simpl.
      destruct (decide (t = tag_occ)) as [->|Hnot].
      * simpl in Hnin. apply not_elem_of_cons in Hnin as [Hkk0 Hnin].
        simpl.         rewrite (IH keys vals i Hlk Hlv ltac:(lia) Hne Hnin).
        rewrite insert_commute; [reflexivity|symmetry; exact Hkk0].
      * simpl. apply (IH keys vals i Hlk Hlv ltac:(lia) Hne Hnin).
Qed.

Lemma contents_overwrite tags keys vals i k v :
  length keys = length tags → length vals = length tags →
  NoDup (occ_keys tags keys) →
  tags !! i = Some tag_occ → keys !! i = Some k →
  (i < length vals)%nat →
  contents_of tags keys (<[i:=v]> vals) = <[k:=v]> (contents_of tags keys vals).
Proof.
  revert keys vals i k v. induction tags as [|t tags IH];
    intros keys vals i k v Hlk Hlv Hdup Ht Hk Hv.
  - simpl in Ht. discriminate.
  - destruct keys as [|k0 keys]; [simpl in Hlk; discriminate|].
    destruct vals as [|v0 vals]; [simpl in Hlv; discriminate|].
    simpl in Hlk, Hlv. injection Hlk as Hlk. injection Hlv as Hlv.
    destruct i as [|i].
    + simpl in Ht, Hk, Hv. injection Ht as Ht. injection Hk as Hk. subst t k0.
      simpl. destruct (decide (tag_occ = tag_occ)) as [_|Hbad];
        [|exfalso; apply Hbad; reflexivity].
      rewrite insert_insert. reflexivity.
    + simpl in Ht, Hk, Hv, Hdup. simpl.
      destruct (decide (t = tag_occ)) as [->|Hnot].
      * simpl in Hdup. apply NoDup_cons in Hdup as [Hnin Hdup].
        assert (k0 ≠ k) as Hne.
        { intros ->. apply Hnin. eapply occ_in; eauto. }
        simpl. rewrite (IH keys vals i k v Hlk Hlv Hdup Ht Hk ltac:(lia)).
        rewrite insert_commute; [reflexivity|exact Hne].
      * simpl. apply (IH keys vals i k v Hlk Hlv Hdup Ht Hk ltac:(lia)).
Qed.

Lemma contents_bury tags keys vals i k v :
  length keys = length tags → length vals = length tags →
  NoDup (occ_keys tags keys) →
  tags !! i = Some tag_occ → keys !! i = Some k → vals !! i = Some v →
  contents_of (<[i:=tag_tomb]> tags) keys vals = delete k (contents_of tags keys vals).
Proof.
  revert keys vals i k v.
  induction tags as [|t tags IH]; intros keys vals i k v Hlk Hlv Hdup Ht Hk Hv.
  - discriminate.
  - destruct keys as [|k0 keys]; [simpl in Hlk; discriminate|].
    destruct vals as [|v0 vals]; [simpl in Hlv; discriminate|].
    simpl in Hlk, Hlv. injection Hlk as Hlk. injection Hlv as Hlv.
    destruct i as [|i].
    + simpl in Ht, Hk, Hv. injection Ht as ->. injection Hk as ->. injection Hv as ->.
      simpl in Hdup. apply NoDup_cons in Hdup as [Hnin Hdup].
      simpl. destruct (decide (tag_tomb = tag_occ)) as [Hbad|_];
        [exfalso; apply tag_tomb_ne_occ; exact Hbad|].
      destruct (decide (tag_occ = tag_occ)) as [_|Hbad];
        [|exfalso; apply Hbad; reflexivity].
      rewrite delete_insert; [reflexivity|].
      apply (contents_none_iff tags keys vals k Hlk Hlv). exact Hnin.
    + simpl in Ht, Hk, Hv, Hdup. simpl.
      destruct (decide (t = tag_occ)) as [->|Hnot].
      * simpl in Hdup. apply NoDup_cons in Hdup as [Hnin Hdup].
        assert (k0 ≠ k) as Hne.
        { intros ->. apply Hnin. eapply occ_in; eauto. }
        simpl. rewrite (IH keys vals i k v Hlk Hlv Hdup Ht Hk Hv).
        rewrite delete_insert_ne; [reflexivity|symmetry; exact Hne].
      * simpl. apply (IH keys vals i k v Hlk Hlv Hdup Ht Hk Hv).
Qed.

Lemma path_ne cap b i j :
  (0 < cap)%nat → (b < cap)%nat → (i < cap)%nat →
  (j < steps_between b i cap)%nat →
  probe_slot b j cap ≠ i.
Proof.
  intros Hcap Hb Hi Hj Heq.
  assert (j < cap)%nat as Hjcap.
  { apply Nat.lt_le_trans with (steps_between b i cap); [exact Hj|].
    apply Nat.lt_le_incl. apply steps_between_lt; done. }
  assert (j = steps_between b i cap) as Heqj.
  { apply (probe_slot_inj b cap j (steps_between b i cap)); try done.
    - apply steps_between_lt; done.
    - rewrite (probe_slot_steps b i cap); done. }
  lia.
Qed.

Lemma no_empty_before_fill cap b idx tags i t :
  t ≠ tag_empty →
  no_empty_before cap b idx tags →
  no_empty_before cap b idx (<[i:=t]> tags).
Proof.
  intros Ht Hold j Hj.
  destruct (decide (i < length tags)%nat) as [Hi|Hi].
  - destruct (decide (probe_slot b j cap = i)) as [Hslot|Hne].
    + rewrite Hslot. rewrite list_lookup_insert; [|done].
      intros Heq. injection Heq as ->. apply Ht. reflexivity.
    + rewrite list_lookup_insert_ne; [|done]. apply Hold. exact Hj.
  - rewrite list_insert_ge; [|lia]. apply Hold. exact Hj.
Qed.

Lemma placed_place cap tags keys i k :
  (0 < cap)%nat →
  length tags = cap → length keys = cap →
  (i < cap)%nat →
  placed cap tags keys →
  no_empty_before cap (bucket k cap) i tags →
  placed cap (<[i:=tag_occ]> tags) (<[i:=k]> keys).
Proof.
  intros Hcap Hltag Hlkey Hi Hplace Hpath i' k' Ht Hk.
  destruct (decide (i' = i)) as [->|Hne].
  -     rewrite list_lookup_insert in Hk; [|lia].
    assert (k' = k) as ->.
    { injection Hk as Hk'. symmetry. exact Hk'. }
    intros j Hj.
    assert (probe_slot (bucket k cap) j cap ≠ i) as Hslot.
    { apply path_ne; try done. apply bucket_lt. done. }
    rewrite list_lookup_insert_ne; [|symmetry; exact Hslot].
    apply Hpath. exact Hj.
  - rewrite list_lookup_insert_ne in Ht; [|symmetry; exact Hne].
    rewrite list_lookup_insert_ne in Hk; [|symmetry; exact Hne].
    apply no_empty_before_fill; [apply tag_occ_ne_empty|].
    apply (Hplace i' k' Ht Hk).
Qed.

Lemma placed_bury cap tags keys i :
  length tags = cap →
  (i < cap)%nat →
  placed cap tags keys →
  placed cap (<[i:=tag_tomb]> tags) keys.
Proof.
  intros Hlen Hi Hplace i' k' Ht Hk.
  destruct (decide (i' = i)) as [->|Hne].
  - rewrite list_lookup_insert in Ht; [|lia].
    injection Ht as Ht. discriminate Ht.
  - rewrite list_lookup_insert_ne in Ht; [|symmetry; exact Hne].
    apply no_empty_before_fill; [apply tag_tomb_ne_empty|].
    apply (Hplace i' k' Ht Hk).
Qed.

Lemma occ_bury_sub tags keys i k' :
  length keys = length tags →
  (i < length tags)%nat →
  tags !! i = Some tag_occ →
  k' ∈ occ_keys (<[i:=tag_tomb]> tags) keys →
  k' ∈ occ_keys tags keys.
Proof.
  revert keys i. induction tags as [|t tags IH]; intros keys i Hlen Hi Ht Hin.
  - simpl in Hi. lia.
  - destruct keys as [|k0 keys]; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    destruct i as [|i].
    + simpl in Ht, Hin. injection Ht as ->. simpl in Hin.
      destruct (decide (tag_tomb = tag_occ)) as [Hbad|].
      { exfalso. apply tag_tomb_ne_occ. exact Hbad. }
      destruct (decide (tag_occ = tag_occ)) as [_|Hbad];
        [|exfalso; apply Hbad; reflexivity].
      simpl. apply elem_of_cons. by right.
    + simpl in Ht, Hin. simpl.
      destruct (decide (t = tag_occ)) as [->|Hnot].
      * simpl in Hin. apply elem_of_cons in Hin as [->|Hin].
        -- apply elem_of_cons. by left.
        -- apply elem_of_cons. right.
           apply (IH keys i).
           { exact Hlen. }
           { simpl in Hi. apply Nat.succ_lt_mono in Hi. exact Hi. }
           { exact Ht. }
           { exact Hin. }
      * apply (IH keys i).
        { exact Hlen. }
        { simpl in Hi. apply Nat.succ_lt_mono in Hi. exact Hi. }
        { exact Ht. }
        { exact Hin. }
Qed.

Lemma nodup_bury tags keys i :
  length keys = length tags →
  (i < length tags)%nat →
  tags !! i = Some tag_occ →
  NoDup (occ_keys tags keys) →
  NoDup (occ_keys (<[i:=tag_tomb]> tags) keys).
Proof.
  revert keys i. induction tags as [|t tags IH]; intros keys i Hlen Hi Ht Hdup.
  - simpl in Hi. lia.
  - destruct keys as [|k0 keys]; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    destruct i as [|i].
    + simpl in Ht, Hdup. injection Ht as ->. simpl in Hdup.
      apply NoDup_cons in Hdup as [_ Hdup]. simpl.
      destruct (decide (tag_tomb = tag_occ)) as [Hbad|];
        [exfalso; apply tag_tomb_ne_occ; exact Hbad|].
      exact Hdup.
    + simpl in Ht, Hdup. simpl.
      destruct (decide (t = tag_occ)) as [->|Hnot].
      * simpl in Hdup. apply NoDup_cons in Hdup as [Hk0 Hdup].
        simpl. apply NoDup_cons. split.
        -- intros Hin. apply Hk0.
           apply (occ_bury_sub tags keys i k0 Hlen).
           { simpl in Hi. apply Nat.succ_lt_mono in Hi. exact Hi. }
           { exact Ht. }
           { exact Hin. }
        -- apply (IH keys i Hlen).
           { simpl in Hi. apply Nat.succ_lt_mono in Hi. exact Hi. }
           { exact Ht. }
           { exact Hdup. }
      * apply (IH keys i Hlen).
        { simpl in Hi. apply Nat.succ_lt_mono in Hi. exact Hi. }
        { exact Ht. }
        { exact Hdup. }
Qed.

Lemma load_bury tags i cap :
  tags !! i = Some tag_occ →
  (2 * count_occ tags ≤ cap)%nat →
  (2 * count_occ (<[i:=tag_tomb]> tags) ≤ cap)%nat.
Proof.
  intros Ht Hle. pose proof (count_bury tags i Ht) as Hc. lia.
Qed.

Lemma size_contents tags keys vals :
  length keys = length tags → length vals = length tags →
  NoDup (occ_keys tags keys) →
  size (contents_of tags keys vals) = count_occ tags.
Proof.
  revert keys vals. induction tags as [|t tags IH]; intros keys vals Hlk Hlv Hdup.
  - destruct keys, vals; simpl in *; try discriminate. done.
  - destruct keys as [|k keys]; [simpl in Hlk; discriminate|].
    destruct vals as [|v vals]; [simpl in Hlv; discriminate|].
    simpl in Hlk, Hlv. injection Hlk as Hlk. injection Hlv as Hlv.
    simpl. destruct (decide (t = tag_occ)) as [->|Hnot].
    + simpl in Hdup. apply NoDup_cons in Hdup as [Hnin Hdup].
      rewrite map_size_insert_None.
      * simpl. rewrite (IH keys vals Hlk Hlv Hdup). lia.
      * apply (contents_none_iff tags keys vals k Hlk Hlv). exact Hnin.
    + simpl in Hdup.
      destruct (decide (t = tag_occ)) as [Hbad|].
      { exfalso. apply Hnot. exact Hbad. }
      simpl. rewrite (IH keys vals Hlk Hlv Hdup). lia.
Qed.

Record wf_table (cap : nat) (tags keys vals : list Z) : Prop := Wf {
  wf_tags_len : length tags = cap;
  wf_keys_len : length keys = cap;
  wf_vals_len : length vals = cap;
  wf_pow : ∃ e, cap = (2 ^ S e)%nat;
  wf_ok : tags_ok tags;
  wf_dup : NoDup (occ_keys tags keys);
  wf_load : (2 * count_occ tags ≤ cap)%nat;
  wf_place : placed cap tags keys
}.

Lemma contents_zeros n :
  contents_of (replicate n 0%Z) (replicate n 0%Z) (replicate n 0%Z) = ∅.
Proof.
  induction n as [|n IH]; simpl; [done|].
  destruct (decide (0%Z = tag_occ)) as [Hbad|].
  - unfold tag_occ in Hbad. lia.
  - exact IH.
Qed.

Lemma count_zeros n : count_occ (replicate n 0%Z) = 0%nat.
Proof.
  induction n as [|n IH]; simpl; [done|].
  destruct (decide (0%Z = tag_occ)) as [Hbad|].
  - unfold tag_occ in Hbad. lia.
  - simpl. exact IH.
Qed.

Lemma occ_zeros n : occ_keys (replicate n 0%Z) (replicate n 0%Z) = [].
Proof.
  induction n as [|n IH]; simpl; [done|].
  destruct (decide (0%Z = tag_occ)) as [Hbad|].
  - unfold tag_occ in Hbad. lia.
  - exact IH.
Qed.

Lemma tags_ok_zeros n : tags_ok (replicate n 0%Z).
Proof.
  apply Forall_replicate. unfold tag_ok, tag_empty. by left.
Qed.

Lemma placed_zeros cap : placed cap (replicate cap 0%Z) (replicate cap 0%Z).
Proof.
  intros i k Ht _. apply lookup_replicate in Ht as [Ht _].
  unfold tag_occ in Ht. lia.
Qed.

Lemma zeros_wf cap :
  (∃ e, cap = (2 ^ S e)%nat) →
  wf_table cap (replicate cap 0%Z) (replicate cap 0%Z) (replicate cap 0%Z).
Proof.
  intros Hpow. apply (Wf cap (replicate cap 0%Z) (replicate cap 0%Z) (replicate cap 0%Z)).
  - rewrite length_replicate. done.
  - rewrite length_replicate. done.
  - rewrite length_replicate. done.
  - exact Hpow.
  - apply tags_ok_zeros.
  - rewrite occ_zeros. constructor.
  - rewrite count_zeros. clear Hpow. lia.
  - apply placed_zeros.
Qed.

Lemma cap_pos cap tags keys vals :
  wf_table cap tags keys vals → (0 < cap)%nat.
Proof.
  intros [_ _ _ [e ->] _ _ _ _]. apply pow_positive.
Qed.

Definition place_slot (tags keys vals : list Z) (idx : nat) (k v : Z) :=
  (<[idx:=tag_occ]> tags, <[idx:=k]> keys, <[idx:=v]> vals).

Definition write_fresh (cap : nat) (tags keys vals : list Z) (k v : Z) :=
  match probe cap (bucket k cap) tags keys vals k with
  | PFound idx _ => (tags, keys, <[idx:=v]> vals)
  | PAbsent idx => place_slot tags keys vals idx k v
  end.

Lemma write_fresh_new cap tags keys vals k v :
  wf_table cap tags keys vals →
  contents_of tags keys vals !! k = None →
  (2 * count_occ tags < cap)%nat →
  ∃ idx,
    write_fresh cap tags keys vals k v =
      (<[idx:=tag_occ]> tags, <[idx:=k]> keys, <[idx:=v]> vals) ∧
    (idx < cap)%nat ∧
    wf_table cap (<[idx:=tag_occ]> tags) (<[idx:=k]> keys) (<[idx:=v]> vals) ∧
    contents_of (<[idx:=tag_occ]> tags) (<[idx:=k]> keys) (<[idx:=v]> vals) =
      <[k:=v]> (contents_of tags keys vals) ∧
    count_occ (<[idx:=tag_occ]> tags) = S (count_occ tags).
Proof.
  intros Hwf Hnone Hroom.
  destruct Hwf as [Hltag Hlkey Hlval Hpow Hok Hdup Hload Hplace].
  assert (0 < cap)%nat as Hcap by (destruct Hpow as [e ->]; apply pow_positive).
  assert (count_occ tags < cap)%nat as Hcount by lia.
  pose proof (probe_shape cap tags keys vals k Hcap Hltag Hlkey Hlval Hok Hdup
                Hplace Hcount) as Hsh.
  unfold write_fresh.
  destruct (probe cap (bucket k cap) tags keys vals k) as [idx found|idx] eqn:Hr.
  - rewrite Hsh in Hnone. discriminate.
  - destruct Hsh as (Hidx & Htag & Hpath & _).
    assert (tags !! idx ≠ Some tag_occ) as Hnot.
    { destruct Htag as [-> | ->].
      - intros Heq. discriminate Heq.
      - intros Heq. discriminate Heq. }
    assert (length keys = length tags) as Hlk.
    { rewrite Hlkey. rewrite Hltag. reflexivity. }
    assert (length vals = length tags) as Hlv.
    { rewrite Hlval. rewrite Hltag. reflexivity. }
    assert (k ∉ occ_keys tags keys) as Hnin.
    { apply (contents_none_iff tags keys vals k Hlk Hlv). exact Hnone. }
    exists idx. split; [reflexivity|]. split; [exact Hidx|]. split; [|split].
    + apply (Wf cap (<[idx:=tag_occ]> tags) (<[idx:=k]> keys) (<[idx:=v]> vals)).
      * rewrite insert_length_eq; [done|lia].
      * rewrite insert_length_eq; [done|lia].
      * rewrite insert_length_eq; [done|lia].
      * exact Hpow.
      * apply tags_ok_insert; [done| |lia]. unfold tag_ok. right. by left.
      * apply nodup_place; [exact Hlk|lia|exact Hdup|exact Hnin|exact Hnot].
      * rewrite count_insert_fresh; [|exact Htag]. apply room_for_one; done.
      * apply placed_place; try done.
    + apply contents_place; [exact Hlk|exact Hlv|lia|exact Hnot|exact Hnin].
    + rewrite count_insert_fresh; [done|exact Htag].
Qed.

Fixpoint rehash_acc (cap : nat) (tags keys vals accT accK accV : list Z)
    : list Z * list Z * list Z :=
  match tags, keys, vals with
  | t :: tags, k :: keys, v :: vals =>
      if decide (t = tag_occ) then
        let '(a, b, c) := write_fresh cap accT accK accV k v in
        rehash_acc cap tags keys vals a b c
      else rehash_acc cap tags keys vals accT accK accV
  | _, _, _ => (accT, accK, accV)
  end.

Lemma rehash_acc_lookup cap tags keys vals accT accK accV :
  wf_table cap accT accK accV →
  length keys = length tags → length vals = length tags →
  tags_ok tags → NoDup (occ_keys tags keys) →
  (∀ x, x ∈ occ_keys tags keys → contents_of accT accK accV !! x = None) →
  (2 * (count_occ accT + count_occ tags) ≤ cap)%nat →
  match rehash_acc cap tags keys vals accT accK accV with
  | (t2, k2, v2) =>
      wf_table cap t2 k2 v2 ∧
      ∀ x, contents_of t2 k2 v2 !! x =
        match contents_of tags keys vals !! x with
        | Some w => Some w
        | None => contents_of accT accK accV !! x
        end
  end.
Proof.
  revert keys vals accT accK accV.
  induction tags as [|t tags IH]; intros keys vals accT accK accV
      Hwf Hlk Hlv Hok Hdup Hdis Hload.
  - destruct keys, vals; simpl in *; try discriminate.
    split; [exact Hwf|]. intros x. simpl. done.
  - destruct keys as [|k keys]; [simpl in Hlk; discriminate|].
    destruct vals as [|v vals]; [simpl in Hlv; discriminate|].
    simpl in Hlk, Hlv. injection Hlk as Hlk. injection Hlv as Hlv.
    apply Forall_cons in Hok as [Htok Hok].
    simpl rehash_acc. simpl contents_of. simpl occ_keys in Hdup, Hdis.
    simpl count_occ in Hload.
    destruct (decide (t = tag_occ)) as [->|Hnot].
    + simpl in Hdup, Hdis. apply NoDup_cons in Hdup as [Hnin Hdup].
      assert (contents_of accT accK accV !! k = None) as Hmiss.
      { apply Hdis. apply elem_of_cons. by left. }
      assert (2 * count_occ accT < cap)%nat as Hroom by lia.
      destruct (write_fresh_new cap accT accK accV k v Hwf Hmiss Hroom)
        as (idx & Heq & _ & Hwf2 & Hins & Hcount).
      rewrite Heq. simpl.
      assert (∀ x, x ∈ occ_keys tags keys →
                contents_of (<[idx:=tag_occ]> accT) (<[idx:=k]> accK)
                  (<[idx:=v]> accV) !! x = None) as Hdis'.
      { intros x Hin. rewrite Hins. rewrite lookup_insert_ne.
        - apply Hdis. apply elem_of_cons. by right.
        - intros ->. apply Hnin. exact Hin. }
      assert (2 * (count_occ (<[idx:=tag_occ]> accT) + count_occ tags) ≤ cap)%nat
        as Hload'.
      { rewrite Hcount. lia. }
      specialize (IH keys vals _ _ _ Hwf2 Hlk Hlv Hok Hdup Hdis' Hload').
      destruct (rehash_acc cap tags keys vals
                  (<[idx:=tag_occ]> accT) (<[idx:=k]> accK) (<[idx:=v]> accV))
        as [[t2 k2] v2].
      destruct IH as [Hwf' Hlook]. split; [exact Hwf'|].
      intros x. rewrite Hlook. rewrite Hins.
      destruct (decide (x = k)) as [->|Hx].
      * assert (contents_of tags keys vals !! k = None) as Htnone.
        { apply (contents_none_iff tags keys vals k Hlk Hlv). exact Hnin. }
        rewrite Htnone. rewrite lookup_insert.
        simpl. destruct (decide (tag_occ = tag_occ)) as [_|Hbad];
          [|exfalso; apply Hbad; reflexivity].
        rewrite lookup_insert. reflexivity.
      * rewrite lookup_insert_ne; [|symmetry; exact Hx].
        simpl.
        destruct (decide (tag_occ = tag_occ)) as [_|Hbad];
          [|exfalso; apply Hbad; reflexivity].
        rewrite lookup_insert_ne; [|symmetry; exact Hx].
        reflexivity.
    + assert (∀ x, x ∈ occ_keys tags keys → contents_of accT accK accV !! x = None)
        as Hdis' by (intros x Hin; apply Hdis; exact Hin).
      assert (2 * (count_occ accT + count_occ tags) ≤ cap)%nat as Hload' by lia.
      specialize (IH keys vals accT accK accV Hwf Hlk Hlv Hok Hdup Hdis' Hload').
      destruct (rehash_acc cap tags keys vals accT accK accV) as [[t2 k2] v2].
      destruct IH as [Hwf' Hlook]. split; [exact Hwf'|].
      intros x. rewrite Hlook. simpl. done.
Qed.

Definition doubled_cap (cap : nat) : nat := (cap + cap)%nat.

Definition grow_table (cap : nat) (tags keys vals : list Z) : list Z * list Z * list Z :=
  let newCap := doubled_cap cap in
  rehash_acc newCap tags keys vals
    (replicate newCap 0%Z) (replicate newCap 0%Z) (replicate newCap 0%Z).

Definition write_remove (cap : nat) (tags keys vals : list Z) (k : Z) :=
  match probe cap (bucket k cap) tags keys vals k with
  | PFound idx _ => (<[idx:=tag_tomb]> tags, keys, vals)
  | PAbsent _ => (tags, keys, vals)
  end.

Lemma write_fresh_found cap tags keys vals k v w :
  wf_table cap tags keys vals →
  contents_of tags keys vals !! k = Some w →
  ∃ idx,
    write_fresh cap tags keys vals k v =
      (tags, keys, <[idx:=v]> vals) ∧
    (idx < cap)%nat ∧
    wf_table cap tags keys (<[idx:=v]> vals) ∧
    contents_of tags keys (<[idx:=v]> vals) = <[k:=v]> (contents_of tags keys vals).
Proof.
  intros Hwf Hsome.
  destruct Hwf as [Hltag Hlkey Hlval Hpow Hok Hdup Hload Hplace].
  assert (0 < cap)%nat as Hcap by (destruct Hpow as [e ->]; apply pow_positive).
  assert (count_occ tags < cap)%nat as Hcount by lia.
  assert (length keys = length tags) as Hlk by (rewrite Hlkey; rewrite Hltag; reflexivity).
  assert (length vals = length tags) as Hlv by (rewrite Hlval; rewrite Hltag; reflexivity).
  assert (k ∈ occ_keys tags keys) as Hin.
  { destruct (contents_none_iff tags keys vals k Hlk Hlv) as [_ Hincl].
    destruct (decide (k ∈ occ_keys tags keys)); [done|].
    exfalso. rewrite (Hincl n) in Hsome. discriminate. }
  destruct (occ_index tags keys k Hin) as (i & Ht & Hk).
  assert (i < cap)%nat as Hi by (apply lookup_lt_Some in Ht; lia).
  destruct (lookup_lt_is_Some_2 vals i) as [old Hv].
  { rewrite Hlval. exact Hi. }
  assert (probe cap (bucket k cap) tags keys vals k = PFound i old) as Hprobe.
  { apply probe_found; try done. }
  unfold write_fresh. rewrite Hprobe. simpl.
  exists i. split; [reflexivity|]. split; [exact Hi|]. split.
  + apply (Wf cap tags keys (<[i:=v]> vals)).
    * done.
    * done.
    * rewrite insert_length_eq; [|rewrite Hlval; exact Hi]. exact Hlval.
    * exact Hpow.
    * exact Hok.
    * exact Hdup.
    * exact Hload.
    * exact Hplace.
  + apply contents_overwrite; [exact Hlk|exact Hlv|exact Hdup|exact Ht|exact Hk|].
    { rewrite Hlval; exact Hi. }
Qed.

Lemma write_remove_spec cap tags keys vals k :
  wf_table cap tags keys vals →
  match write_remove cap tags keys vals k with
  | (t2, k2, v2) =>
      wf_table cap t2 k2 v2 ∧
      contents_of t2 k2 v2 = delete k (contents_of tags keys vals)
  end.
Proof.
  intros Hwf.
  destruct Hwf as [Hltag Hlkey Hlval Hpow Hok Hdup Hload Hplace].
  assert (0 < cap)%nat as Hcap by (destruct Hpow as [e ->]; apply pow_positive).
  assert (count_occ tags < cap)%nat as Hcount by lia.
  assert (length keys = length tags) as Hlk by (rewrite Hlkey; rewrite Hltag; reflexivity).
  assert (length vals = length tags) as Hlv by (rewrite Hlval; rewrite Hltag; reflexivity).
  unfold write_remove.
  destruct (probe cap (bucket k cap) tags keys vals k) as [idx v|idx] eqn:Hr.
  - set (b := bucket k cap).
    assert (b < cap)%nat as Hb by (unfold b; apply bucket_lt; destruct Hpow as [e ->]; apply pow_positive).
    assert (probe_prefix cap b 0 tags keys k None) as Hpre by (apply prefix_zero; lia).
    pose proof (probe_from_inv cap b 0 cap tags keys vals k None Hcap Hb eq_refl
                  Hltag Hlkey Hlval Hok Hcount Hpre) as Hslot.
    unfold probe in Hr. rewrite Hr in Hslot.
    destruct Hslot as (Hidx & Ht & Hk & Hv & _).
    split.
    + apply (Wf cap (<[idx:=tag_tomb]> tags) keys vals).
      * rewrite insert_length_eq; [done|rewrite Hltag; exact Hidx].
      * done. * done. * exact Hpow.
      * apply tags_ok_insert; [exact Hok| |rewrite Hltag; exact Hidx].
        unfold tag_ok. right. right. reflexivity.
      * apply nodup_bury; [exact Hlk|rewrite Hltag; exact Hidx|exact Ht|exact Hdup].
      * apply load_bury; [exact Ht|exact Hload].
      * apply placed_bury; [exact Hltag|exact Hidx|exact Hplace].
    + exact (contents_bury tags keys vals idx k v Hlk Hlv Hdup Ht Hk Hv).
  - pose proof (probe_shape cap tags keys vals k Hcap Hltag Hlkey Hlval Hok Hdup
                  Hplace Hcount) as Habs.
    rewrite Hr in Habs. destruct Habs as (_ & _ & _ & Hnone).
    split.
    + constructor; [exact Hltag|exact Hlkey|exact Hlval|exact Hpow|exact Hok|exact Hdup|lia|exact Hplace].
    + apply map_eq. intros z.
      destruct (decide (z = k)) as [->|Hne].
      * rewrite lookup_delete. exact Hnone.
      * rewrite lookup_delete_ne; [reflexivity|done].
Qed.

Lemma doubled_cap_pow cap e :
  cap = (2 ^ S e)%nat → doubled_cap cap = (2 ^ S (S e))%nat.
Proof.
  intros ->. unfold doubled_cap. apply double_pow.
Qed.

Lemma rehash_acc_sound cap tags keys vals accT accK accV t2 k2 v2 :
  rehash_acc cap tags keys vals accT accK accV = ((t2, k2), v2) →
  wf_table cap accT accK accV →
  length keys = length tags → length vals = length tags →
  tags_ok tags → NoDup (occ_keys tags keys) →
  (∀ x, x ∈ occ_keys tags keys → contents_of accT accK accV !! x = None) →
  (2 * (count_occ accT + count_occ tags) ≤ cap)%nat →
  wf_table cap t2 k2 v2 ∧
  ∀ x, contents_of t2 k2 v2 !! x =
    match contents_of tags keys vals !! x with
    | Some w => Some w
    | None => contents_of accT accK accV !! x
    end.
Proof.
  intros Heq Hwf Hlk Hlv Hok Hdup Hdis Hload.
  pose proof (rehash_acc_lookup cap tags keys vals accT accK accV
               Hwf Hlk Hlv Hok Hdup Hdis Hload) as Hspec.
  rewrite Heq in Hspec. simpl in Hspec. exact Hspec.
Qed.

Lemma grow_table_spec cap tags keys vals e :
  cap = (2 ^ S e)%nat →
  wf_table cap tags keys vals →
  match grow_table cap tags keys vals with
  | (t2, k2, v2) =>
      wf_table (doubled_cap cap) t2 k2 v2 ∧
      contents_of t2 k2 v2 = contents_of tags keys vals
  end.
Proof.
  intros Hcap Hwf.
  destruct (grow_table cap tags keys vals) as ((t2 & k2) & v2) eqn:Hg.
  simpl. destruct Hwf as [Hltag Hlkey Hlval _ Hok Hdup Hload _].
  unfold grow_table in *.
  set (newCap := doubled_cap cap).
  assert (newCap = (2 ^ S (S e))%nat) as HnewCap.
  { unfold newCap. rewrite (doubled_cap_pow cap e Hcap). reflexivity. }
  assert (wf_table newCap (replicate newCap 0%Z) (replicate newCap 0%Z) (replicate newCap 0%Z))
    as Hempty by (apply zeros_wf; exists (S e); exact HnewCap).
  assert (2 * (count_occ (replicate newCap 0%Z) + count_occ tags) ≤ newCap)%nat as Hroom.
  { rewrite count_zeros. unfold newCap, doubled_cap. lia. }
  assert (∀ x, x ∈ occ_keys tags keys →
            contents_of (replicate newCap 0%Z) (replicate newCap 0%Z) (replicate newCap 0%Z) !! x = None)
    as Hdis.
  { intros x Hin. rewrite contents_zeros. done. }
  assert (length keys = length tags) as Hlen by (rewrite Hlkey; rewrite Hltag; reflexivity).
  assert (length vals = length tags) as Hlv by (rewrite Hlval; rewrite Hltag; reflexivity).
  unfold grow_table in Hg. simpl in Hg.
  destruct (rehash_acc_sound newCap tags keys vals
              (replicate newCap 0%Z) (replicate newCap 0%Z) (replicate newCap 0%Z)
              t2 k2 v2 Hg Hempty Hlen Hlv Hok Hdup Hdis Hroom) as [Hwf' Hlook].
  constructor; [exact Hwf'|].
  apply map_eq; intro x.
  destruct (contents_of tags keys vals !! x) as [w|] eqn:Ho.
  - rewrite (Hlook x). rewrite Ho. simpl. reflexivity.
  - rewrite (Hlook x). rewrite Ho. simpl. rewrite contents_zeros. reflexivity.
Qed.

Open Scope expr_scope.

Section hash_map.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  Definition sld (z : Z) : expr :=
    StackLoad (Val (LitV (LitStack z))).
  Definition sas (z : Z) (e : expr) : expr :=
    StackAssign (Val (LitV (LitStack z))) e.

  Definition nonneg_while (lh cap : Z) : expr :=
    While (sld lh ≤ Val (LitV (LitInt (-1))))
      (sas lh (sld lh + Val (LitV (LitInt cap)))).

  Definition below_while (lh cap : Z) : expr :=
    While (Val (LitV (LitInt cap)) ≤ sld lh)
      (sas lh (sld lh - Val (LitV (LitInt cap)))).

  Lemma wp_nonneg (lh : Z) (h0 cap : Z) :
    (0 < cap)%Z →
    StackId lh ↦ₛ LitV (LitInt h0) -∗
    WP nonneg_while lh cap
      {{ _, ∃ h', ⌜ h' = bring_nonneg (Z.to_nat (Z.max 0 (- h0))) h0 cap ⌝ ∗
                   StackId lh ↦ₛ LitV (LitInt h') }}.
  Proof.
    intros Hcap.
    remember (Z.to_nat (Z.max 0 (- h0))) as fuel eqn:Hfuel.
    revert h0 Hfuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros h0 Hfuel.
    iIntros "Hh".
    unfold nonneg_while.
    iApply wp_while.
    iApply (wp_bind [IfCtx
      (Seq (sas lh (sld lh + Val (LitV (LitInt cap)))) (nonneg_while lh cap))
      (Val (LitV LitUnit))]).
    iApply (wp_bind [BinOpLCtx LeOp (Val (LitV (LitInt (-1))))]).
    iApply (wp_stack_load (StackId lh) with "Hh").
    iIntros "!> _ Hh".
    iApply wp_binop.
    { reflexivity. }
    iIntros "!> _".
    destruct fuel as [|fuel].
    - assert (Z.to_nat (Z.max 0 (- h0)) = 0)%nat as Hz by (symmetry; exact Hfuel).
      apply z_to_nat_0 in Hz.
      assert (bool_decide (h0 ≤ -1)%Z = false) as ->.
      { apply bool_decide_eq_false. lia. }
      iApply wp_if_false.
      iApply wp_value'.
      iExists h0. iFrame "Hh". iPureIntro. reflexivity.
    - assert (h0 < 0)%Z as Hn.
      { assert (0 < Z.to_nat (Z.max 0 (- h0)))%nat as Hpos by (rewrite <- Hfuel; lia).
        destruct (Z_lt_le_dec h0 0) as [Hlt|Hge]; [exact Hlt|].
        assert (Z.max 0 (- h0) = 0)%Z as Heq by (rewrite Z.max_l; lia).
        rewrite Heq in Hpos. simpl in Hpos. lia. }
      assert (bool_decide (h0 ≤ -1)%Z = true) as ->.
      { apply bool_decide_eq_true. lia. }
      iApply wp_if_true.
      iApply (wp_bind [SeqCtx (nonneg_while lh cap)]).
      iApply (wp_bind [StackAssignRCtx (LitV (LitStack lh))]).
      iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt cap)))]).
      iApply (wp_stack_load (StackId lh) with "Hh").
      iIntros "!> _ Hh".
      iApply wp_binop.
      { reflexivity. }
      iIntros "!> _".
      iApply (wp_stack_assign with "Hh").
      iIntros "!> _ Hh".
      iApply wp_seq.
      fold nonneg_while.
      set (y := Z.to_nat (Z.max 0 (- (h0 + cap)))).
      assert (y < S fuel)%nat as Hlt.
      { unfold y. rewrite Hfuel.
        assert (Z.max 0 (- h0) = - h0)%Z as -> by (rewrite Z.max_r; lia).
        destruct (Z_lt_le_dec (h0 + cap) 0) as [Hstill|Hdone].
        - assert (Z.max 0 (- (h0 + cap)) = (- h0 - cap))%Z as -> by (rewrite Z.max_r; lia).
          assert (Z.to_nat (- h0) = (Z.to_nat (- h0 - cap) + Z.to_nat cap)%nat) as Hsum.
          { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
          assert (1 ≤ Z.to_nat cap)%nat as Hone.
          { replace 1%nat with (Z.to_nat 1%Z) by reflexivity.
            apply Z2Nat.inj_le; lia. }
          lia.
        - assert (Z.max 0 (- (h0 + cap)) = 0)%Z as -> by (rewrite Z.max_l; lia).
          lia. }
      iApply (wp_wand with "[Hh]").
      { iApply (IH y Hlt (h0 + cap)%Z eq_refl with "Hh"). }
      iIntros (_) "(%h' & %Heq & Hh)".
      iExists h'. iFrame "Hh". iPureIntro.
      rewrite Heq. unfold y. symmetry. rewrite Hfuel.
      apply bring_nonneg_step; [exact Hcap|exact Hn].
  Qed.

  Lemma wp_below (lh : Z) (h0 cap : Z) :
    (0 < cap)%Z → (0 ≤ h0)%Z →
    StackId lh ↦ₛ LitV (LitInt h0) -∗
    WP below_while lh cap
      {{ _, ∃ h', ⌜ h' = bring_below (Z.to_nat h0) h0 cap ⌝ ∗
                   StackId lh ↦ₛ LitV (LitInt h') }}.
  Proof.
    intros Hcap Hnn0.
    remember (Z.to_nat h0) as fuel eqn:Hfuel.
    revert h0 Hnn0 Hfuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros h0 Hnn Hfuel.
    iIntros "Hh".
    unfold below_while.
    iApply wp_while.
    iApply (wp_bind [IfCtx
      (Seq (sas lh (sld lh - Val (LitV (LitInt cap)))) (below_while lh cap))
      (Val (LitV LitUnit))]).
    iApply (wp_bind [BinOpRCtx LeOp (LitV (LitInt cap))]).
    iApply (wp_stack_load (StackId lh) with "Hh").
    iIntros "!> _ Hh".
    iApply wp_binop.
    { reflexivity. }
    iIntros "!> _".
    destruct fuel as [|fuel].
    - assert (Z.to_nat h0 = 0)%nat as Hz by (symmetry; exact Hfuel).
      apply z_to_nat_0 in Hz.
      assert (bool_decide (cap ≤ h0)%Z = false) as ->.
      { apply bool_decide_eq_false. lia. }
      iApply wp_if_false.
      iApply wp_value'.
      iExists h0. iFrame "Hh". iPureIntro. reflexivity.
    - destruct (Z_lt_le_dec h0 cap) as [Hlt|Hge].
      + assert (bool_decide (cap ≤ h0)%Z = false) as ->.
        { apply bool_decide_eq_false. lia. }
        iApply wp_if_false.
        iApply wp_value'.
        iExists h0. iFrame "Hh". iPureIntro.
        assert (bring_below (Z.to_nat h0) h0 cap = h0) as Heq
          by (apply bring_below_finished; [exact Hnn|exact Hlt]).
        rewrite <- Hfuel in Heq. symmetry. exact Heq.
      + assert (bool_decide (cap ≤ h0)%Z = true) as ->.
        { apply bool_decide_eq_true. exact Hge. }
        iApply wp_if_true.
        iApply (wp_bind [SeqCtx (below_while lh cap)]).
        iApply (wp_bind [StackAssignRCtx (LitV (LitStack lh))]).
        iApply (wp_bind [BinOpLCtx MinusOp (Val (LitV (LitInt cap)))]).
        iApply (wp_stack_load (StackId lh) with "Hh").
        iIntros "!> _ Hh".
        iApply wp_binop.
        { reflexivity. }
        iIntros "!> _".
        iApply (wp_stack_assign with "Hh").
        iIntros "!> _ Hh".
        iApply wp_seq.
        fold below_while.
        set (y := Z.to_nat (h0 - cap)).
        assert (0 ≤ h0 - cap)%Z as Hnn' by lia.
        assert (y < S fuel)%nat as Hlty.
        { unfold y. rewrite Hfuel.
          assert (Z.to_nat h0 = (Z.to_nat (h0 - cap) + Z.to_nat cap)%nat) as Hsum.
          { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
          assert (1 ≤ Z.to_nat cap)%nat as Hone.
          { replace 1%nat with (Z.to_nat 1%Z) by reflexivity.
            apply Z2Nat.inj_le; lia. }
          lia. }
        iApply (wp_wand with "[Hh]").
        { iApply (IH y Hlty (h0 - cap)%Z Hnn' eq_refl with "Hh"). }
        iIntros (_) "(%h' & %Heq & Hh)".
        iExists h'. iFrame "Hh". iPureIntro.
        rewrite Heq. symmetry. rewrite Hfuel.
        apply bring_below_step; [exact Hcap|exact Hnn|exact Hge].
  Qed.

  Definition residue_inner : expr :=
    Seq (While (Var "rem" ≤ Val (LitV (LitInt (-1))))
           (Assign "rem" (Var "rem" + Var "cap")))
      (Seq (While (Var "cap" ≤ Var "rem")
             (Assign "rem" (Var "rem" - Var "cap")))
        (Var "rem")).

  Definition residue_body : expr :=
    Let (Some "k") (StructLoad (Var "args") 0)
      (Let (Some "cap") (StructLoad (Var "args") 1)
        (VarBind "rem" (Var "k") residue_inner)).

  Definition call_residue (k cap : Z) : expr :=
    App (Val (RecV None (Some "args") residue_body))
      (Val (StructV [LitV (LitInt k); LitV (LitInt cap)])).

  Definition residue_run (lh : Z) : expr := subst_var "rem" lh residue_inner.

  Lemma residue_after_bind (lh : Z) :
    subst_var "rem" lh residue_inner = residue_run lh.
  Proof. reflexivity. Qed.

  Lemma subst_cap_residue (cap : Z) :
    subst "cap" (LitV (LitInt cap)) residue_inner =
    Seq (While (Var "rem" ≤ Val (LitV (LitInt (-1))))
           (Assign "rem" (Var "rem" + Val (LitV (LitInt cap)))))
      (Seq (While (Val (LitV (LitInt cap)) ≤ Var "rem")
             (Assign "rem" (Var "rem" - Val (LitV (LitInt cap)))))
        (Var "rem")).
  Proof.
    cbn [subst]. f_equal; repeat f_equal; reflexivity.
  Qed.

  Lemma cap_residue_stack (lslot cap : Z) :
    subst_var "rem" lslot (subst "cap" (LitV (LitInt cap)) residue_inner) =
    Seq (nonneg_while lslot cap) (Seq (below_while lslot cap) (sld lslot)).
  Proof.
    unfold nonneg_while, below_while, sld, sas.
    rewrite subst_cap_residue. cbn [subst_var]. f_equal; reflexivity.
  Qed.

  Lemma residue_run_wp (lslot : Z) (key cap : Z) :
    (0 < cap)%Z →
    StackId lslot ↦ₛ LitV (LitInt key) -∗
    WP (Seq (nonneg_while lslot cap) (Seq (below_while lslot cap) (sld lslot)))
      {{ v, ⌜ v = LitV (LitInt (residue key cap)) ⌝ ∗
           StackId lslot ↦ₛ LitV (LitInt (residue key cap)) }}.
  Proof.
    intros Hcap. set (r := residue key cap).
    iIntros "Hh".
    iApply (wp_bind [SeqCtx (Seq (below_while lslot cap) (sld lslot))]).
    iApply (wp_wand with "[Hh]").
    { iApply (wp_nonneg with "Hh"). exact Hcap. }
    iIntros (w) "(%h1 & %Hh1 & Hh)".
    assert (0 ≤ h1)%Z as Hnn1.
    { rewrite Hh1. apply (proj1 (bring_nonneg_spec key cap (Z.to_nat (Z.max 0 (- key))) Hcap ltac:(lia))). }
    iApply wp_seq.
    iApply (wp_bind [SeqCtx (sld lslot)]).
    iApply (wp_wand with "[Hh]").
    { iApply (wp_below lslot h1 cap Hcap Hnn1 with "Hh"). }
    iIntros (w') "(%h2 & %Hh2 & Hh)".
    iApply wp_seq.
    iApply (wp_stack_load (StackId lslot) with "Hh").
    iIntros "!> _".
    assert (h2 = r)%Z as Heqr.
    { rewrite /r. unfold residue. rewrite Hh1 in Hh2. exact Hh2. }
    iIntros "Hstack".
    rewrite Heqr. iFrame. done.
  Qed.

  Lemma residue_wp (k cap : Z) :
    (0 < cap)%Z →
    ⊢ WP call_residue k cap {{ v, ⌜ v = LitV (LitInt (residue k cap)) ⌝ }}.
  Proof.
    intros Hcap. unfold call_residue, residue_body. hm_pure.
    iApply wp_var_bind. iIntros (lr) "Hr".
    rewrite cap_residue_stack.
    iApply (wp_wand with "[Hr]").
    { iApply (residue_run_wp lr k cap Hcap with "Hr"). }
    iIntros (r) "[%Hr Hslot]".
    iExists (LitV (LitInt (residue k cap))). iFrame. done.
  Qed.


  (** * Imperative [HashMap] *)

  Definition lit_tag_empty : expr := Val (LitV (LitInt tag_empty)).
  Definition lit_tag_occ : expr := Val (LitV (LitInt tag_occ)).
  Definition lit_tag_tomb : expr := Val (LitV (LitInt tag_tomb)).
  Definition lit_m1 : expr := Val (LitV (LitInt (-1))).

  Definition arr_len (a : expr) : expr :=
    App (Rec None (Some "a") array.length_body) a.

  Definition arr_get (a i : expr) : expr :=
    App (Rec None (Some "args") array.get_body) (Struct [] [a; i]).

  Definition arr_set (a i x : expr) : expr :=
    App (Rec None (Some "args") array.set_body) (Struct [] [a; i; x]).

  Definition make_zero_array : expr :=
    Let (Some "p") (Alloc (Val (LitV (LitInt (Z.of_nat default_capacity)))))
      (New [] [Val (LitV (LitInt (Z.of_nat default_capacity))); Var "p"]).

  Definition is_hm_slots (cap : nat) (tags keys vals : list Z)
      (ta ka va : val_cjr) : iProp Σ :=
    is_array tags ta ∗ is_array keys ka ∗ is_array vals va ∗
    ⌜ length tags = cap ⌝ ∗ ⌜ length keys = cap ⌝ ∗ ⌜ length vals = cap ⌝ ∗
    ⌜ wf_table cap tags keys vals ⌝.

  Definition is_hashmap (m : gmap Z Z) (cap : nat) (a : val_cjr) : iProp Σ :=
    ∃ o sz ta ka va tags keys vals,
      ⌜ a = LitV (LitObj o) ⌝ ∗
      ⌜ contents_of tags keys vals = m ⌝ ∗
      ⌜ sz = Z.of_nat (count_occ tags) ⌝ ∗
      ObjId o ↦ₒ[0] LitV (LitInt sz) ∗
      ObjId o ↦ₒ[1] ta ∗
      ObjId o ↦ₒ[2] ka ∗
      ObjId o ↦ₒ[3] va ∗
      is_hm_slots cap tags keys vals ta ka va.

  Lemma is_array_obj_hm xs a :
    is_array xs a -∗ ∃ o, ⌜ a = LitV (LitObj o) ⌝ ∗ is_array xs a.
  Proof.
    iIntros "Ha". iDestruct "Ha" as (o base) "(%Ha & Hlen & Hptr & Hblk & Hcells)".
    iExists o. iSplit; [done|]. iExists o, base. iSplit; [done|]. iFrame.
  Qed.

  Lemma wp_new_step vs v es Φ :
    WP New (vs ++ [v]) es {{ Φ }} ⊢ WP New vs (Val v :: es) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done| | |].
    { intros σ. eexists [], (New (vs ++ [v]) es), σ, []. constructor. }
    { intros ????? Hstep. inversion Hstep; simplify_eq; auto. }
    iIntros "!> _". iApply "H".
  Qed.

  Definition init_body : expr :=
    Let (Some "tags") make_zero_array
      (Let (Some "keys") make_zero_array
        (Let (Some "vals") make_zero_array
          (New [] [Val (LitV (LitInt 0)); Var "tags"; Var "keys"; Var "vals"]))).

  Definition call_init : expr :=
    App (Rec None None init_body) (Val (LitV LitUnit)).

  Definition size_body : expr := FieldLoad (Var "m") 0.
  Definition call_size (m : val_cjr) : expr :=
    App (Rec None (Some "m") size_body) (Val m).

  Definition capacity_body : expr :=
    Let (Some "tags") (FieldLoad (Var "m") 1) (FieldLoad (Var "tags") 0).
  Definition call_capacity (m : val_cjr) : expr :=
    App (Rec None (Some "m") capacity_body) (Val m).

  Definition is_empty_body : expr :=
    BinOp EqOp (FieldLoad (Var "m") 0) (Val (LitV (LitInt 0))).
  Definition call_is_empty (m : val_cjr) : expr :=
    App (Rec None (Some "m") is_empty_body) (Val m).

  Definition probe_slot_e (start step cap : expr) : expr :=
    If (BinOp LeOp (BinOp PlusOp (BinOp PlusOp start step) (Val (LitV (LitInt 1)))) cap)
      (BinOp PlusOp start step)
      (BinOp MinusOp (BinOp PlusOp start step) cap).

  Definition probe_done (found slot value : expr) : expr :=
    Struct [] [found; slot; value].

  Definition hole_or_e (hole fallback : expr) : expr :=
    If (BinOp EqOp hole lit_m1) fallback hole.

  Definition scan_call_e (fuel start step cap tags keys vals key hole : expr) : expr :=
    App (Var "scan") (Struct [] [fuel; start; step; cap; tags; keys; vals; key; hole]).

  Definition scan_loop : expr :=
    If (BinOp LeOp (Var "fuel") (Val (LitV (LitInt 0))))
      (probe_done (Val (LitV (LitBool false)))
        (hole_or_e (Var "hole") (Var "start")) (Val (LitV (LitInt 0))))
      (Let (Some "slot") (probe_slot_e (Var "start") (Var "step") (Var "cap"))
        (Let (Some "tag") (arr_get (Var "tags") (Var "slot"))
          (If (BinOp EqOp (Var "tag") lit_tag_empty)
            (probe_done (Val (LitV (LitBool false)))
              (hole_or_e (Var "hole") (Var "slot")) (Val (LitV (LitInt 0))))
            (If (BinOp EqOp (Var "tag") lit_tag_occ)
              (Let (Some "key") (arr_get (Var "keys") (Var "slot"))
                (If (BinOp EqOp (Var "key") (Var "k"))
                  (probe_done (Val (LitV (LitBool true))) (Var "slot")
                    (arr_get (Var "vals") (Var "slot")))
                  (scan_call_e (Var "fuel" - Val (LitV (LitInt 1)))
                    (Var "start") (Var "step" + Val (LitV (LitInt 1)))
                    (Var "cap") (Var "tags") (Var "keys") (Var "vals")
                    (Var "k") (Var "hole"))))
              (scan_call_e (Var "fuel" - Val (LitV (LitInt 1)))
                (Var "start") (Var "step" + Val (LitV (LitInt 1)))
                (Var "cap") (Var "tags") (Var "keys") (Var "vals")
                (Var "k") (hole_or_e (Var "hole") (Var "slot"))))))).

  Definition scan_body : expr :=
    Let (Some "fuel") (StructLoad (Var "args") 0)
      (Let (Some "start") (StructLoad (Var "args") 1)
      (Let (Some "step") (StructLoad (Var "args") 2)
      (Let (Some "cap") (StructLoad (Var "args") 3)
      (Let (Some "tags") (StructLoad (Var "args") 4)
      (Let (Some "keys") (StructLoad (Var "args") 5)
      (Let (Some "vals") (StructLoad (Var "args") 6)
      (Let (Some "k") (StructLoad (Var "args") 7)
      (Let (Some "hole") (StructLoad (Var "args") 8)
      (scan_loop))))))))).

  Definition scan_v : val_cjr := RecV (Some "scan") (Some "args") scan_body.

  Definition zlit (x : Z) : expr := Val (LitV (LitInt x)).
  Definition nlit (n : nat) : expr := zlit (Z.of_nat n).
  Definition hole_z (h : option nat) : Z :=
    match h with None => -1 | Some i => Z.of_nat i end.
  Definition probe_val (r : probe_out) : val_cjr :=
    match r with
    | PFound i v => StructV [LitV (LitBool true); LitV (LitInt (Z.of_nat i)); LitV (LitInt v)]
    | PAbsent i => StructV [LitV (LitBool false); LitV (LitInt (Z.of_nat i)); LitV (LitInt 0)]
    end.

  Definition call_scan (fuel start step cap : nat) (ta ka va : val_cjr)
      (key : Z) (hole : option nat) : expr :=
    App (Val scan_v) (Val (StructV
      [LitV (LitInt (Z.of_nat fuel)); LitV (LitInt (Z.of_nat start));
       LitV (LitInt (Z.of_nat step)); LitV (LitInt (Z.of_nat cap));
       ta; ka; va; LitV (LitInt key); LitV (LitInt (hole_z hole))])).

  Definition buffer_probe_body : expr :=
    Let (Some "tags") (StructLoad (Var "args") 0)
    (Let (Some "keys") (StructLoad (Var "args") 1)
    (Let (Some "vals") (StructLoad (Var "args") 2)
    (Let (Some "cap") (StructLoad (Var "args") 3)
    (Let (Some "k") (StructLoad (Var "args") 4)
    (Let (Some "start")
      (App (Val (RecV None (Some "args") residue_body)) (Struct [] [Var "k"; Var "cap"]))
      (App (Val scan_v) (Struct [] [Var "cap"; Var "start"; zlit 0; Var "cap";
        Var "tags"; Var "keys"; Var "vals"; Var "k"; lit_m1]))))))).

  Definition buffer_probe_e (ta ka va cap k : expr) : expr :=
    App (Val (RecV None (Some "args") buffer_probe_body))
      (Struct [] [ta; ka; va; cap; k]).
  Definition call_buffer_probe ta ka va cap k : expr :=
    App (Val (RecV None (Some "args") buffer_probe_body))
      (Val (StructV [ta; ka; va; LitV (LitInt (Z.of_nat cap)); LitV (LitInt k)])).

  Definition put_body : expr :=
    Let (Some "tags") (StructLoad (Var "args") 0)
    (Let (Some "keys") (StructLoad (Var "args") 1)
    (Let (Some "vals") (StructLoad (Var "args") 2)
    (Let (Some "cap") (StructLoad (Var "args") 3)
    (Let (Some "k") (StructLoad (Var "args") 4)
    (Let (Some "v") (StructLoad (Var "args") 5)
    (Let (Some "res") (buffer_probe_e (Var "tags") (Var "keys") (Var "vals") (Var "cap") (Var "k"))
    (Let (Some "idx") (StructLoad (Var "res") 1)
      (If (StructLoad (Var "res") 0)
        (arr_set (Var "vals") (Var "idx") (Var "v"))
        (Seq (arr_set (Var "tags") (Var "idx") lit_tag_occ)
          (Seq (arr_set (Var "keys") (Var "idx") (Var "k"))
            (arr_set (Var "vals") (Var "idx") (Var "v")))))))))))).

  Definition put_e (ta ka va cap k v : expr) : expr :=
    App (Val (RecV None (Some "args") put_body)) (Struct [] [ta; ka; va; cap; k; v]).
  Definition call_put ta ka va cap k v : expr :=
    App (Val (RecV None (Some "args") put_body))
      (Val (StructV [ta; ka; va; LitV (LitInt (Z.of_nat cap)); LitV (LitInt k); LitV (LitInt v)])).

  Definition probe_open : expr :=
    Let (Some "tags") (FieldLoad (Var "m") 1)
      (Let (Some "keys") (FieldLoad (Var "m") 2)
        (Let (Some "vals") (FieldLoad (Var "m") 3)
          (Let (Some "cap") (arr_len (Var "tags"))
            (Let (Some "bargs") (Struct [] [Var "k"; Var "cap"])
              (Let (Some "start") (App (Val (RecV None (Some "args") residue_body)) (Var "bargs"))
                (App (Rec (Some "scan") (Some "args") scan_body)
                  (Struct [] [Var "cap"; Var "start"; zlit 0; Var "cap";
                    Var "tags"; Var "keys"; Var "vals"; Var "k"; lit_m1]))))))).

  Definition probe_for_body : expr :=
    Let (Some "m") (StructLoad (Var "args") 0)
      (Let (Some "k") (StructLoad (Var "args") 1) probe_open).

  Definition call_probe (m : val_cjr) (k : Z) : expr :=
    App (Val (RecV None (Some "args") probe_for_body))
      (Val (StructV [m; LitV (LitInt k)])).

  Definition call_probe_e (m k : expr) : expr :=
    App (Val (RecV None (Some "args") probe_for_body)) (Struct [] [m; k]).

  Definition contains_body : expr :=
    Let (Some "m") (StructLoad (Var "args") 0)
      (Let (Some "k") (StructLoad (Var "args") 1)
        (Let (Some "res") (call_probe_e (Var "m") (Var "k"))
          (StructLoad (Var "res") 0))).

  Definition call_contains (m : val_cjr) (k : Z) : expr :=
    App (Rec None (Some "args") contains_body)
      (Val (StructV [m; LitV (LitInt k)])).

  Definition get_body : expr :=
    Let (Some "m") (StructLoad (Var "args") 0)
      (Let (Some "k") (StructLoad (Var "args") 1)
        (Let (Some "res") (call_probe_e (Var "m") (Var "k"))
          (Struct [] [StructLoad (Var "res") 0; StructLoad (Var "res") 2]))).

  Definition call_get (m : val_cjr) (k : Z) : expr :=
    App (Rec None (Some "args") get_body)
      (Val (StructV [m; LitV (LitInt k)])).

  Lemma default_cap_pow : ∃ e, default_capacity = (2 ^ S e)%nat.
  Proof. exists 3%nat. reflexivity. Qed.

  Lemma make_zero_spec :
    ⊢ WP make_zero_array {{ a, is_array (replicate default_capacity 0%Z) a }}.
  Proof.
    unfold make_zero_array.
    iApply (wp_bind [LetCtx (Some "p")
      (New [] [Val (LitV (LitInt (Z.of_nat default_capacity))); Var "p"])]).
    iApply (wp_alloc (Z.of_nat default_capacity)).
    { unfold default_capacity. done. }
    iIntros (base) "Hcells".
    iIntros "Hblk".
    iEval (rewrite Nat2Z.id) in "Hblk".
    iEval (rewrite Nat2Z.id) in "Hcells".
    iApply wp_let. simpl.
    iApply wp_new_step. simpl.
    iApply wp_new_step. simpl.
    iApply wp_new. iIntros (o) "Harr".
    iDestruct "Harr" as "[Hlen [Hptr _]]".
    iExists o, base. iSplit; [done|].
    iFrame "Hlen Hptr Hblk".
    iApply (seq_zero_cells base default_capacity with "Hcells").
  Qed.

  Lemma init_spec :
    ⊢ WP call_init {{ m, is_hashmap ∅ default_capacity m }}.
  Proof.
    unfold call_init, init_body. hm_pure.
    hm_take. iApply (wp_wand with "[]"). { iApply make_zero_spec. }
    iIntros (ta) "Ht".
    iDestruct (is_array_obj_hm with "Ht") as (ot) "(%Ht & Ht)". subst ta.
    hm_pure.
    hm_take. iApply (wp_wand with "[]"). { iApply make_zero_spec. }
    iIntros (ka) "Hk".
    iDestruct (is_array_obj_hm with "Hk") as (ok) "(%Hk & Hk)". subst ka.
    hm_pure.
    hm_take. iApply (wp_wand with "[]"). { iApply make_zero_spec. }
    iIntros (va) "Hv".
    iDestruct (is_array_obj_hm with "Hv") as (ov) "(%Hv & Hv)". subst va.
    hm_pure.
    iApply wp_new. iIntros (o) "Hfields".
    iEval (simpl) in "Hfields".
    iDestruct "Hfields" as "(Hsz & Hta & Hka & Hva & _)".
    iExists o, 0%Z, (LitV (LitObj ot)), (LitV (LitObj ok)), (LitV (LitObj ov)),
      (replicate default_capacity 0%Z), (replicate default_capacity 0%Z),
      (replicate default_capacity 0%Z).
    rewrite contents_zeros count_zeros. iFrame.
    iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    unfold is_hm_slots. iFrame. iPureIntro.
    split; [apply length_replicate|].
    split; [apply length_replicate|].
    split; [apply length_replicate|].
    apply zeros_wf. apply default_cap_pow.
  Qed.

  Lemma size_spec m cap (a : val_cjr) :
    is_hashmap m cap a -∗
    WP call_size a {{ v, ⌜ v = LitV (LitInt (Z.of_nat (size m))) ⌝ ∗ is_hashmap m cap a }}.
  Proof.
    iIntros "Hm".
    iDestruct "Hm" as (o sz ta ka va tags keys vals)
      "(%Ha & %Hmap & %Hsz & Hsize & Hta & Hka & Hva & Hslots)".
    subst a sz. iDestruct "Hslots" as "(Ht & Hk & Hv & %Lt & %Lk & %Lv & %Hwf)".
    assert (size m = count_occ tags) as Hcount.
    { rewrite <- Hmap. apply size_contents; try lia. exact (wf_dup _ _ _ _ Hwf). }
    unfold call_size, size_body. hm_pure. hm_read.
    iSplit; [by rewrite Hcount|].
    iExists o, (Z.of_nat (count_occ tags)), ta, ka, va, tags, keys, vals.
    iFrame. repeat iSplit; try done.
  Qed.

  Lemma capacity_spec m cap (a : val_cjr) :
    is_hashmap m cap a -∗
    WP call_capacity a {{ v, ⌜ v = LitV (LitInt (Z.of_nat cap)) ⌝ ∗ is_hashmap m cap a }}.
  Proof.
    iIntros "Hm".
    iDestruct "Hm" as (o sz ta ka va tags keys vals)
      "(%Ha & %Hmap & %Hsz & Hsize & Hta & Hka & Hva & Hslots)".
    subst a sz. iDestruct "Hslots" as "(Ht & Hk & Hv & %Lt & %Lk & %Lv & %Hwf)".
    iDestruct "Ht" as (ot base) "(%Hta & Hlen & Hptr & Hblk & Hcells)". subst ta.
    unfold call_capacity, capacity_body. hm_pure. hm_read. hm_pure. hm_read.
    iSplit; [by rewrite Lt|].
    iExists o, (Z.of_nat (count_occ tags)), (LitV (LitObj ot)), ka, va, tags, keys, vals.
    iFrame. repeat iSplit; try done.
  Qed.

  Lemma is_empty_spec m cap (a : val_cjr) :
    is_hashmap m cap a -∗
    WP call_is_empty a
      {{ v, ⌜ v = LitV (LitBool (bool_decide (size m = 0%nat))) ⌝ ∗ is_hashmap m cap a }}.
  Proof.
    iIntros "Hm".
    iDestruct "Hm" as (o sz ta ka va tags keys vals)
      "(%Ha & %Hmap & %Hsz & Hsize & Hta & Hka & Hva & Hslots)".
    subst a sz. iDestruct "Hslots" as "(Ht & Hk & Hv & %Lt & %Lk & %Lv & %Hwf)".
    assert (size m = count_occ tags) as Hcount.
    { rewrite <- Hmap. apply size_contents; try lia. exact (wf_dup _ _ _ _ Hwf). }
    unfold call_is_empty, is_empty_body. hm_pure. hm_read. hm_pure.
    iSplit.
    { iPureIntro. f_equal. f_equal. apply bool_decide_ext. rewrite Hcount. lia. }
    iExists o, (Z.of_nat (count_occ tags)), ta, ka, va, tags, keys, vals.
    iFrame. repeat iSplit; try done.
  Qed.

  Lemma arr_get_spec xs a i x :
    xs !! i = Some x → is_array xs a -∗
    WP arr_get (Val a) (nlit i)
      {{ r, ⌜ r = LitV (LitInt x) ⌝ ∗ is_array xs a }}.
  Proof.
    intros Hi. iIntros "Ha".
    iDestruct "Ha" as (o base) "(%Ha & Hlen & Hptr & Hblk & Hcells)". subst a.
    unfold arr_get, nlit, zlit. hm_pure. hm_read. hm_pure.
    iDestruct (big_sepL_lookup_acc with "Hcells") as "[Hi Hclose]"; [exact Hi|].
    iApply (wp_load with "Hi"). iIntros "!> _ Hi".
    iDestruct ("Hclose" with "Hi") as "Hcells".
    iSplit; [done|]. iExists o, base. iSplit; [done|]. iFrame.
  Qed.

  Lemma arr_set_spec xs a i old x :
    xs !! i = Some old → is_array xs a -∗
    WP arr_set (Val a) (nlit i) (zlit x)
      {{ r, ⌜ r = LitV LitUnit ⌝ ∗ is_array (<[i:=x]> xs) a }}.
  Proof.
    intros Hi. iIntros "Ha".
    assert (length (<[i:=x]> xs) = length xs) as Hlen by
      (apply length_insert; eapply lookup_lt_Some; exact Hi).
    iDestruct "Ha" as (o base) "(%Ha & Hn & Hptr & Hblk & Hcells)". subst a.
    unfold arr_set, nlit, zlit. hm_pure. hm_read. hm_pure.
    iDestruct (big_sepL_insert_acc with "Hcells") as "[Hi Hclose]"; [exact Hi|].
    iApply (wp_store with "Hi"). iIntros "!> _ Hi".
    iDestruct ("Hclose" $! x with "Hi") as "Hcells".
    iSplit; [done|]. iExists o, base. iSplit; [done|].
    rewrite Hlen. iFrame.
  Qed.

  Lemma probe_slot_e_spec start step cap :
    (0 < cap)%nat → (start < cap)%nat → (step < cap)%nat →
    ⊢ WP probe_slot_e (nlit start) (nlit step) (nlit cap)
      {{ r, ⌜ r = LitV (LitInt (Z.of_nat (probe_slot start step cap))) ⌝ }}.
  Proof.
    intros Hcap Hstart Hstep. unfold probe_slot_e, nlit, zlit. hm_pure.
    rewrite (probe_slot_sub start step cap Hcap Hstart Hstep).
    destruct (decide ((start + step) < cap)%nat) as [Hlt|Hge].
    - rewrite bool_decide_eq_true_2; [|lia]. iApply wp_if_true. hm_pure.
      iPureIntro. do 2 f_equal. lia.
    - rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false. hm_pure.
      iPureIntro. do 2 f_equal. rewrite Nat2Z.inj_sub; lia.
  Qed.

  Lemma hole_or_e_spec hole fallback :
    ⊢ WP hole_or_e (zlit (hole_z hole)) (nlit fallback)
      {{ r, ⌜ r = LitV (LitInt (Z.of_nat (hole_or hole fallback))) ⌝ }}.
  Proof.
    destruct hole as [h|]; unfold hole_or_e, hole_z, hole_or, nlit, zlit, lit_m1;
      hm_pure.
    - rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false. hm_pure. done.
    - iApply wp_if_true. hm_pure. done.
  Qed.

  Lemma scan_spec fuel :
    ∀ start step cap ta ka va tags keys vals k hole,
    (0 < cap)%nat → (start < cap)%nat → (step + fuel ≤ cap)%nat →
    length tags = cap → length keys = cap → length vals = cap →
    is_array tags ta -∗ is_array keys ka -∗ is_array vals va -∗
    WP call_scan fuel start step cap ta ka va k hole
      {{ r, ⌜ r = probe_val (probe_from fuel start step cap tags keys vals k hole) ⌝ ∗
            is_array tags ta ∗ is_array keys ka ∗ is_array vals va }}.
  Proof.
    induction fuel as [|fuel IH]; intros start step cap ta ka va tags keys vals k hole
      Hcap Hstart Hbound Lt Lk Lv; iIntros "Ht Hk Hv";
      iDestruct (is_array_obj_hm with "Ht") as (ot) "(%Ht & Ht)";
      iDestruct (is_array_obj_hm with "Hk") as (ok) "(%Hk & Hk)";
      iDestruct (is_array_obj_hm with "Hv") as (ov) "(%Hv & Hv)";
      subst ta ka va;
      unfold call_scan, scan_v, scan_body, scan_loop, scan_call_e, probe_done;
      hm_pure.
    - iApply wp_if_true. hm_pure. destruct hole as [h|]; simpl.
      + rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false. hm_pure. iFrame. done.
      + iApply wp_if_true. hm_pure. iFrame. done.
    - iApply wp_if_false.
      hm_take. iApply (wp_wand with "[]").
      { iApply probe_slot_e_spec; lia. }
      iIntros (r) "%Hr". subst r. hm_admin.
      set (idx := probe_slot start step cap).
      assert (idx < cap)%nat as Hidx by (unfold idx; apply probe_slot_lt; done).
      destruct (lookup_lt_is_Some_2 tags idx) as [tag Htag]; [lia|].
      hm_take. iApply (wp_wand with "[Ht]").
      { iApply (arr_get_spec tags _ idx tag Htag with "Ht"). }
      iIntros (r) "[%Hr Ht]". subst r. hm_admin.
      change (tags !! probe_slot start step cap = Some tag) in Htag.
      cbn [probe_from]. rewrite Htag.
      destruct (decide (tag = tag_empty)) as [He|He].
      + rewrite bool_decide_eq_true_2; [|exact He]. iApply wp_if_true.
        iApply array.wp_struct_step. simpl.
        iApply (wp_bind [StructCtx [LitV (LitBool false)] [zlit 0]]).
        iApply (wp_wand with "[]"). { iApply hole_or_e_spec. }
        iIntros (r) "%Hr". subst r. hm_admin. iFrame. done.
      + rewrite bool_decide_eq_false_2; [|exact He]. iApply wp_if_false. hm_admin.
        destruct (decide (tag = tag_occ)) as [Ho|Ho].
        * rewrite bool_decide_eq_true_2; [|exact Ho]. iApply wp_if_true. hm_admin.
          destruct (lookup_lt_is_Some_2 keys idx) as [key Hkey]; [lia|].
          destruct (lookup_lt_is_Some_2 vals idx) as [value Hval]; [lia|].
          hm_take. iApply (wp_wand with "[Hk]").
          { iApply (arr_get_spec keys _ idx key Hkey with "Hk"). }
          iIntros (r) "[%Hr Hk]". subst r. hm_admin.
          change (keys !! probe_slot start step cap = Some key) in Hkey.
          change (vals !! probe_slot start step cap = Some value) in Hval.
          rewrite Hkey Hval.
          destruct (decide (key = k)) as [Hhit|Hmiss].
          -- rewrite bool_decide_eq_true_2; [|exact Hhit]. iApply wp_if_true. hm_admin.
             iApply (wp_bind [StructCtx
               [LitV (LitBool true); LitV (LitInt (Z.of_nat idx))] []]).
             iApply (wp_wand with "[Hv]").
             { iApply (arr_get_spec vals _ idx value Hval with "Hv"). }
             iIntros (r) "[%Hr Hv]". subst r. hm_admin. iFrame. done.
          -- rewrite bool_decide_eq_false_2; [|exact Hmiss]. iApply wp_if_false. hm_admin.
             replace (Z.of_nat (S fuel) - 1)%Z with (Z.of_nat fuel) by lia.
             replace (Z.of_nat step + 1)%Z with (Z.of_nat (S step)) by lia.
             iApply (IH start (S step) cap _ _ _ tags keys vals k hole with "Ht Hk Hv"); try done; lia.
        * rewrite bool_decide_eq_false_2; [|exact Ho]. iApply wp_if_false. hm_admin.
          destruct hole as [h|]; simpl.
          -- rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false. hm_admin.
             replace (Z.of_nat (S fuel) - 1)%Z with (Z.of_nat fuel) by lia.
             replace (Z.of_nat step + 1)%Z with (Z.of_nat (S step)) by lia.
             iApply (IH start (S step) cap _ _ _ tags keys vals k (Some h) with "Ht Hk Hv"); try done; lia.
          -- iApply wp_if_true. hm_admin.
             replace (Z.of_nat (S fuel) - 1)%Z with (Z.of_nat fuel) by lia.
             replace (Z.of_nat step + 1)%Z with (Z.of_nat (S step)) by lia.
             iApply (IH start (S step) cap _ _ _ tags keys vals k (Some idx) with "Ht Hk Hv"); try done; lia.
  Qed.

  Lemma buffer_probe_spec cap ta ka va tags keys vals k :
    (0 < cap)%nat → length tags = cap → length keys = cap → length vals = cap →
    is_array tags ta -∗ is_array keys ka -∗ is_array vals va -∗
    WP call_buffer_probe ta ka va cap k
      {{ r, ⌜ r = probe_val (probe cap (bucket k cap) tags keys vals k) ⌝ ∗
        is_array tags ta ∗ is_array keys ka ∗ is_array vals va }}.
  Proof.
    intros Hcap Lt Lk Lv. iIntros "Ht Hk Hv".
    iDestruct (is_array_obj_hm with "Ht") as (ot) "(%Ht & Ht)".
    iDestruct (is_array_obj_hm with "Hk") as (ok) "(%Hk & Hk)".
    iDestruct (is_array_obj_hm with "Hv") as (ov) "(%Hv & Hv)". subst ta ka va.
    unfold call_buffer_probe, buffer_probe_body. iApply wp_app. simpl. hm_admin.
    try try hm_take. hm_admin. iApply (wp_wand with "[]").
    { iApply residue_wp. lia. }
    iIntros (r) "%Hr". subst r. hm_admin.
    replace (residue k (Z.of_nat cap)) with (Z.of_nat (bucket k cap)) by
      (unfold bucket; rewrite Z2Nat.id; pose proof (residue_spec k (Z.of_nat cap) ltac:(lia)); lia).
    iApply (scan_spec cap (bucket k cap) 0 cap _ _ _ tags keys vals k None with "Ht Hk Hv");
      try done; try (apply bucket_lt; done); lia.
  Qed.

  Lemma probe_slots cap tags keys vals k :
    wf_table cap tags keys vals →
    match probe cap (bucket k cap) tags keys vals k with
    | PFound i v => (i < cap)%nat ∧ tags !! i = Some tag_occ ∧
        keys !! i = Some k ∧ vals !! i = Some v
    | PAbsent i => (i < cap)%nat ∧
        (tags !! i = Some tag_empty ∨ tags !! i = Some tag_tomb)
    end.
  Proof.
    intros Hwf. pose proof (cap_pos _ _ _ _ Hwf) as Hcap.
    assert (count_occ tags < cap)%nat as Hcount by (pose proof (wf_load _ _ _ _ Hwf); lia).
    pose proof (probe_from_inv cap (bucket k cap) 0 cap tags keys vals k None Hcap
      (bucket_lt k cap Hcap) eq_refl (wf_tags_len _ _ _ _ Hwf)
      (wf_keys_len _ _ _ _ Hwf) (wf_vals_len _ _ _ _ Hwf) (wf_ok _ _ _ _ Hwf)
      Hcount (prefix_zero cap (bucket k cap) tags keys k ltac:(pose proof (bucket_lt k cap Hcap); lia))) as Hinfo.
    unfold probe. destruct (probe_from cap (bucket k cap) 0 cap tags keys vals k None); simpl in *; tauto.
  Qed.

  Lemma put_spec cap ta ka va tags keys vals k v :
    wf_table cap tags keys vals →
    is_array tags ta -∗ is_array keys ka -∗ is_array vals va -∗
    WP call_put ta ka va cap k v
      {{ r, let '(t2,k2,v2) := write_fresh cap tags keys vals k v in
        ⌜ r = LitV LitUnit ⌝ ∗ is_array t2 ta ∗ is_array k2 ka ∗ is_array v2 va }}.
  Proof.
    intros Hwf. iIntros "Ht Hk Hv".
    iDestruct (is_array_obj_hm with "Ht") as (ot) "(%Ht & Ht)".
    iDestruct (is_array_obj_hm with "Hk") as (ok) "(%Hk & Hk)".
    iDestruct (is_array_obj_hm with "Hv") as (ov) "(%Hv & Hv)". subst ta ka va.
    unfold call_put, put_body. iApply wp_app. simpl. hm_admin.
    try hm_take. hm_admin. iApply (wp_wand with "[Ht Hk Hv]").
    { iApply (buffer_probe_spec with "Ht Hk Hv");
        [eapply cap_pos; exact Hwf|apply (wf_tags_len _ _ _ _ Hwf)|
         apply (wf_keys_len _ _ _ _ Hwf)|apply (wf_vals_len _ _ _ _ Hwf)]. }
    iIntros (r) "(%Hr & Ht & Hk & Hv)". subst r.
    pose proof (probe_slots cap tags keys vals k Hwf) as Hslots.
    unfold write_fresh. destruct (probe cap (bucket k cap) tags keys vals k) as [idx old|idx]; simpl in *.
    - destruct Hslots as (Hi & Htag & Hkey & Hval). hm_admin. iApply wp_if_true. hm_admin.
      iApply (wp_wand with "[Hv]"). { iApply (arr_set_spec vals _ idx old v Hval with "Hv"). }
      iIntros (r) "[%Hr Hv]". iFrame. done.
    - destruct Hslots as [Hi Htag].
      destruct (lookup_lt_is_Some_2 tags idx) as [tag Htidx]; [rewrite (wf_tags_len _ _ _ _ Hwf); done|].
      destruct (lookup_lt_is_Some_2 keys idx) as [key Hkidx]; [rewrite (wf_keys_len _ _ _ _ Hwf); done|].
      destruct (lookup_lt_is_Some_2 vals idx) as [old Hvidx]; [rewrite (wf_vals_len _ _ _ _ Hwf); done|].
      hm_admin. iApply wp_if_false. hm_admin.
      iApply (wp_bind [SeqCtx _]).
      iApply (wp_wand with "[Ht]"). { iApply (arr_set_spec tags _ idx tag tag_occ Htidx with "Ht"). }
      iIntros (r) "[%Hr Ht]". subst r. hm_admin.
      iApply (wp_bind [SeqCtx _]).
      iApply (wp_wand with "[Hk]"). { iApply (arr_set_spec keys _ idx key k Hkidx with "Hk"). }
      iIntros (r) "[%Hr Hk]". subst r. hm_admin.
      iApply (wp_wand with "[Hv]"). { iApply (arr_set_spec vals _ idx old v Hvidx with "Hv"). }
      iIntros (r) "[%Hr Hv]". unfold place_slot. iFrame. done.
  Qed.

  Definition rehash_body : expr := Let (Some "fuel") (StructLoad (Var "args") 0)
    (Let (Some "i") (StructLoad (Var "args") 1)
      (Let (Some "st") (StructLoad (Var "args") 2)
        (Let (Some "sk") (StructLoad (Var "args") 3)
          (Let (Some "sv") (StructLoad (Var "args") 4)
            (Let (Some "cap") (StructLoad (Var "args") 5)
              (Let (Some "dt") (StructLoad (Var "args") 6)
                (Let (Some "dk") (StructLoad (Var "args") 7)
                  (Let (Some "dv") (StructLoad (Var "args") 8)
                    (If (Var "fuel" ≤ zlit 0) (Val (LitV LitUnit))
                      (Let (Some "tag") (arr_get (Var "st") (Var "i"))
                        (Seq
                        (If (BinOp EqOp (Var "tag") lit_tag_occ)
                        (Let (Some "key") (arr_get (Var "sk") (Var "i"))
                        (Let (Some "value") (arr_get (Var "sv") (Var "i")) (put_e (Var "dt") (Var "dk") (Var "dv") (Var "cap") (Var "key") (Var "value")))) (Val (LitV LitUnit))) (App (Var "rehash") (Struct [] [Var "fuel" - zlit 1; Var "i" + zlit 1; Var "st"; Var "sk"; Var "sv"; Var "cap"; Var "dt"; Var "dk"; Var "dv"]))))))))))))).
  Definition rehash_v : val_cjr := RecV (Some "rehash") (Some "args") rehash_body.
  Definition call_rehash fuel i st sk sv cap dt dk dv : expr :=
    App (Val rehash_v) (Val (StructV [LitV (LitInt (Z.of_nat fuel)); LitV (LitInt (Z.of_nat i)); st; sk; sv; LitV (LitInt (Z.of_nat cap)); dt; dk; dv])).
  Definition grow_body : expr := Let (Some "m") (StructLoad (Var "args") 0)
    (Let (Some "min") (StructLoad (Var "args") 1)
      (Let (Some "tags") (FieldLoad (Var "m") 1)
        (Let (Some "keys") (FieldLoad (Var "m") 2)
          (Let (Some "vals") (FieldLoad (Var "m") 3)
            (Let (Some "cap") (arr_len (Var "tags"))
              (Let (Some "newCap") (Var "cap" + Var "cap")
                (Let (Some "ntags") (App (Rec None (Some "n") array.make_body) (Var "newCap"))
                  (Let (Some "nkeys") (App (Rec None (Some "n") array.make_body) (Var "newCap"))
                    (Let (Some "nvals") (App (Rec None (Some "n") array.make_body) (Var "newCap"))
                      (Seq (App (Val rehash_v) (Struct [] [Var "cap"; zlit 0; Var "tags"; Var "keys"; Var "vals"; Var "newCap"; Var "ntags"; Var "nkeys"; Var "nvals"]))
                        (Seq (FieldStore (Var "m") 1 (Var "ntags"))
                        (Seq (FieldStore (Var "m") 2 (Var "nkeys")) (FieldStore (Var "m") 3 (Var "nvals")))))))))))))).
  Definition call_grow m minCap : expr := App (Val (RecV None (Some "args") grow_body)) (Val (StructV [m; LitV (LitInt minCap)])).
  Definition grow_e m minCap : expr := App (Val (RecV None (Some "args") grow_body)) (Struct [] [m; minCap]).
  Definition add_room_body : expr := Let (Some "m") (StructLoad (Var "args") 0)
    (Let (Some "k") (StructLoad (Var "args") 1)
      (Let (Some "v") (StructLoad (Var "args") 2)
        (Let (Some "found") (StructLoad (Var "args") 3)
          (Let (Some "tags") (FieldLoad (Var "m") 1)
            (Let (Some "keys") (FieldLoad (Var "m") 2)
              (Let (Some "vals") (FieldLoad (Var "m") 3)
                (Let (Some "cap") (arr_len (Var "tags"))
                  (Seq (put_e (Var "tags") (Var "keys") (Var "vals") (Var "cap") (Var "k") (Var "v"))
                    (If (Var "found") (Val (LitV LitUnit))
                      (Let (Some "sz") (FieldLoad (Var "m") 0) (FieldStore (Var "m") 0 (Var "sz" + zlit 1)))))))))))).
  Definition call_add_room m k v found : expr := App (Val (RecV None (Some "args") add_room_body)) (Val (StructV [m; LitV (LitInt k); LitV (LitInt v); LitV (LitBool found)])).
  Definition add_room_e m k v found : expr := App (Val (RecV None (Some "args") add_room_body)) (Struct [] [m; k; v; found]).
  Definition add_body : expr := Let (Some "m") (StructLoad (Var "args") 0)
    (Let (Some "k") (StructLoad (Var "args") 1)
      (Let (Some "v") (StructLoad (Var "args") 2)
        (Let (Some "res") (call_probe_e (Var "m") (Var "k"))
          (Let (Some "found") (StructLoad (Var "res") 0)
            (If (Var "found") (add_room_e (Var "m") (Var "k") (Var "v") (Var "found"))
              (Let (Some "sz") (App (Rec None (Some "m") size_body) (Var "m"))
                (Let (Some "cap") (App (Rec None (Some "m") capacity_body) (Var "m"))
                  (Seq
                    (If (Var "cap" ≤ Var "sz" + Var "sz") (grow_e (Var "m") (Var "cap" + zlit 1)) (Val (LitV LitUnit))) (add_room_e (Var "m") (Var "k") (Var "v") (Var "found")))))))))).
  Definition call_add m k v : expr := App (Val (RecV None (Some "args") add_body)) (Val (StructV [m; LitV (LitInt k); LitV (LitInt v)])).
  Definition remove_body : expr := Let (Some "m") (StructLoad (Var "args") 0)
    (Let (Some "k") (StructLoad (Var "args") 1)
      (Let (Some "tags") (FieldLoad (Var "m") 1)
        (Let (Some "keys") (FieldLoad (Var "m") 2)
          (Let (Some "vals") (FieldLoad (Var "m") 3)
            (Let (Some "cap") (arr_len (Var "tags"))
              (Let (Some "res") (buffer_probe_e (Var "tags") (Var "keys") (Var "vals") (Var "cap") (Var "k"))
                (If (StructLoad (Var "res") 0)
                  (Let (Some "idx") (StructLoad (Var "res") 1)
                    (Let (Some "old") (StructLoad (Var "res") 2)
                      (Seq (arr_set (Var "tags") (Var "idx") lit_tag_tomb)
                        (Let (Some "sz") (FieldLoad (Var "m") 0)
                        (Seq (FieldStore (Var "m") 0 (Var "sz" - zlit 1)) (Var "old")))))) (zlit 0)))))))).
  Definition call_remove m k : expr := App (Val (RecV None (Some "args") remove_body)) (Val (StructV [m; LitV (LitInt k)])).

  Lemma head_drop_hm {A} (xs : list A) i x tail :
    drop i xs = x :: tail → xs !! i = Some x ∧ drop (S i) xs = tail.
  Proof.
    revert xs. induction i as [|i IH]; intros [|y xs] H; simpl in *;
      try discriminate; [by inversion H|apply IH; exact H].
  Qed.

  Lemma rehash_spec tags :
    ∀ keys vals i st sk sv sta ska sva cap dt dk dv accT accK accV,
    drop i st = tags → drop i sk = keys → drop i sv = vals →
    length keys = length tags → length vals = length tags →
    tags_ok tags → NoDup (occ_keys tags keys) →
    wf_table cap accT accK accV →
    (∀ x, x ∈ occ_keys tags keys → contents_of accT accK accV !! x = None) →
    (2 * (count_occ accT + count_occ tags) ≤ cap)%nat →
    is_array st sta -∗ is_array sk ska -∗ is_array sv sva -∗
    is_array accT dt -∗ is_array accK dk -∗ is_array accV dv -∗
    WP call_rehash (length tags) i sta ska sva cap dt dk dv
      {{ r, let '(t2,k2,v2) := rehash_acc cap tags keys vals accT accK accV in
        ⌜r = LitV LitUnit⌝ ∗ is_array st sta ∗ is_array sk ska ∗ is_array sv sva ∗
        is_array t2 dt ∗ is_array k2 dk ∗ is_array v2 dv }}.
  Proof.
    induction tags as [|tag tags IH]; intros keys vals i st sk sv sta ska sva cap dt dk dv accT accK accV
      Hdt Hdk Hdv Hlk Hlv Hok Hdup Hwf Hdis Hload;
      iIntros "Hst Hsk Hsv Ht Hk Hv";
      iDestruct (is_array_obj_hm with "Hst") as (ost) "(%Hsta & Hst)";
      iDestruct (is_array_obj_hm with "Hsk") as (osk) "(%Hska & Hsk)";
      iDestruct (is_array_obj_hm with "Hsv") as (osv) "(%Hsva & Hsv)";
      iDestruct (is_array_obj_hm with "Ht") as (ot) "(%Hdta & Ht)";
      iDestruct (is_array_obj_hm with "Hk") as (ok) "(%Hdka & Hk)";
      iDestruct (is_array_obj_hm with "Hv") as (ov) "(%Hdva & Hv)";
      subst sta ska sva dt dk dv;
      unfold call_rehash, rehash_v, rehash_body; iApply wp_app; simpl; hm_admin.
    - destruct keys, vals; simpl in *; try discriminate.
      iApply wp_if_true. hm_admin. iFrame. done.
    - destruct keys as [|key keys]; [simpl in Hlk; discriminate|].
      destruct vals as [|value vals]; [simpl in Hlv; discriminate|].
      simpl in Hlk, Hlv. injection Hlk as Hlk. injection Hlv as Hlv.
      apply Forall_cons in Hok as [Htok Hok].
      destruct (head_drop_hm _ _ _ _ Hdt) as [Htag Hdt'];
      destruct (head_drop_hm _ _ _ _ Hdk) as [Hkey Hdk'];
      destruct (head_drop_hm _ _ _ _ Hdv) as [Hvalue Hdv'].
      iApply wp_if_false. hm_admin. hm_take.
      iApply (wp_wand with "[Hst]"). { iApply (arr_get_spec st _ i tag Htag with "Hst"). }
      iIntros (r) "[%Hr Hst]". subst r. hm_admin.
      simpl rehash_acc. simpl occ_keys in Hdup, Hdis. simpl count_occ in Hload.
      destruct (decide (tag = tag_occ)) as [->|Hnot].
      + rewrite bool_decide_eq_true_2; [|done]. iApply wp_if_true. hm_admin.
        hm_take. iApply (wp_wand with "[Hsk]").
        { iApply (arr_get_spec sk _ i key Hkey with "Hsk"). }
        iIntros (r) "[%Hr Hsk]". subst r. hm_admin.
        hm_take. iApply (wp_wand with "[Hsv]").
        { iApply (arr_get_spec sv _ i value Hvalue with "Hsv"). }
        iIntros (r) "[%Hr Hsv]". subst r. hm_admin.
        apply NoDup_cons in Hdup as [Hnin Hdup].
        assert (contents_of accT accK accV !! key = None) as Hmiss.
        { apply Hdis. apply elem_of_cons. by left. }
        destruct (write_fresh_new cap accT accK accV key value Hwf Hmiss ltac:(lia))
          as (idx & Hwrite & Hidx & Hwf2 & Hins & Hcount).
        iApply (wp_wand with "[Ht Hk Hv]"). { iApply (put_spec with "Ht Hk Hv"). exact Hwf. }
        iIntros (r) "Hslots". iEval (rewrite Hwrite) in "Hslots".
        iDestruct "Hslots" as "(%Hr & Ht & Hk & Hv)". subst r. hm_admin.
        replace (Z.of_nat (S (length tags)) - 1)%Z with (Z.of_nat (length tags)) by lia.
        replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by lia.
        rewrite Hwrite. simpl.
        iApply (IH keys vals (S i) st sk sv _ _ _ cap _ _ _ _ _ _
          Hdt' Hdk' Hdv' Hlk Hlv Hok Hdup Hwf2 with "Hst Hsk Hsv Ht Hk Hv").
        * intros x Hin. rewrite Hins. rewrite lookup_insert_ne.
          -- apply Hdis. apply elem_of_cons. by right.
          -- intros ->. apply Hnin. exact Hin.
        * rewrite Hcount. lia.
      + rewrite bool_decide_eq_false_2; [|done]. iApply wp_if_false. hm_admin.
        replace (Z.of_nat (S (length tags)) - 1)%Z with (Z.of_nat (length tags)) by lia.
        replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by lia.
        iApply (IH keys vals (S i) st sk sv _ _ _ cap _ _ _ accT accK accV
          Hdt' Hdk' Hdv' Hlk Hlv Hok Hdup Hwf Hdis with "Hst Hsk Hsv Ht Hk Hv"). lia.
  Qed.

  Lemma write_fresh_effect cap tags keys vals k v :
    wf_table cap tags keys vals →
    (contents_of tags keys vals !! k = None → (2 * count_occ tags < cap)%nat) →
    let '(t2,k2,v2) := write_fresh cap tags keys vals k v in
    wf_table cap t2 k2 v2 ∧
    contents_of t2 k2 v2 = <[k:=v]> (contents_of tags keys vals) ∧
    count_occ t2 = if bool_decide (is_Some (contents_of tags keys vals !! k))
                  then count_occ tags else S (count_occ tags).
  Proof.
    intros Hwf Hroom. destruct (contents_of tags keys vals !! k) as [w|] eqn:Hlookup.
    - destruct (write_fresh_found cap tags keys vals k v w Hwf Hlookup)
        as (i & -> & Hi & Hwf2 & Hcontents). simpl. auto.
    - destruct (write_fresh_new cap tags keys vals k v Hwf Hlookup (Hroom eq_refl))
        as (i & -> & Hi & Hwf2 & Hcontents & Hcount). simpl. auto.
  Qed.

  Lemma add_room_spec m cap a k v found :
    found = bool_decide (is_Some (m !! k)) →
    (m !! k = None → (2 * size m < cap)%nat) →
    is_hashmap m cap a -∗
    WP call_add_room a k v found
      {{ r, ⌜ r = LitV LitUnit ⌝ ∗ is_hashmap (<[k:=v]> m) cap a }}.
  Proof.
    intros Hfound Hroom. iIntros "Hm".
    iDestruct "Hm" as (o sz ta ka va tags keys vals)
      "(%Ha & %Hm & %Hsz & Hsz & Hta & Hka & Hva & Hslots)".
    iDestruct "Hslots" as "(Ht & Hk & Hv & %Lt & %Lk & %Lv & %Hwf)".
    iDestruct (is_array_obj_hm with "Ht") as (ot) "(%Ht & Ht)".
    iDestruct (is_array_obj_hm with "Hk") as (ok) "(%Hk & Hk)".
    iDestruct (is_array_obj_hm with "Hv") as (ov) "(%Hv & Hv)".
    subst a ta ka va sz m.
    assert (size (contents_of tags keys vals) = count_occ tags) as Hsize.
    { apply size_contents; [lia|lia|exact (wf_dup _ _ _ _ Hwf)]. }
    rewrite Hsize in Hroom.
    pose proof (write_fresh_effect cap tags keys vals k v Hwf Hroom) as Heffect.
    destruct (write_fresh cap tags keys vals k v) as [[t2 k2] v2] eqn:Hwrite.
    destruct Heffect as (Hwf2 & Hcontents & Hcount).
    rewrite <- Hfound in Hcount.
    unfold call_add_room, add_room_body. iApply wp_app. simpl. hm_admin.
    hm_read. hm_admin. hm_read. hm_admin. hm_read. hm_admin.
    hm_take. iApply (wp_wand with "[Ht]"). { iApply (array.length_spec with "Ht"). }
    iIntros (r) "[%Hr Ht]". subst r. rewrite Lt. hm_admin.
    iApply (wp_wand with "[Ht Hk Hv]"). { iApply (put_spec with "Ht Hk Hv"). exact Hwf. }
    iIntros (r) "Hslots". iEval (rewrite Hwrite) in "Hslots".
    iDestruct "Hslots" as "(%Hr & Ht & Hk & Hv)". subst r. hm_admin.
    destruct found.
    - iApply wp_if_true. hm_admin. iSplit; [done|].
      iExists o, (Z.of_nat (count_occ tags)), (LitV (LitObj ot)), (LitV (LitObj ok)),
        (LitV (LitObj ov)), t2, k2, v2. unfold is_hm_slots.
      iFrame. repeat iSplit; try done; iPureIntro; first [lia|apply Hwf2].
    - iApply wp_if_false. hm_admin. hm_read. hm_admin.
      hm_write.
      replace (Z.of_nat (count_occ tags) + 1)%Z with (Z.of_nat (count_occ t2)) by (rewrite Hcount; lia).
      iSplit; [done|]. iExists o, (Z.of_nat (count_occ t2)), (LitV (LitObj ot)),
        (LitV (LitObj ok)), (LitV (LitObj ov)), t2, k2, v2.
      unfold is_hm_slots. iFrame. repeat iSplit; try done; iPureIntro; first [lia|apply Hwf2].
  Qed.

  Lemma probe_spec m cap (a : val_cjr) (k : Z) :
    is_hashmap m cap a -∗
    WP call_probe a k
      {{ res, ∃ found idx v,
          ⌜ res = StructV [LitV (LitBool found); LitV (LitInt (Z.of_nat idx)); LitV (LitInt v)] ⌝ ∗
          ⌜ m !! k = if found then Some v else None ⌝ ∗
          ⌜ found = false → v = 0%Z ⌝ ∗
          is_hashmap m cap a }}.
  Proof.
    iIntros "Hm". iDestruct "Hm" as
      (o sz ta ka va tags keys vals) "(%Ha & %Hm & %Hsz & Hsz & Hta & Hka & Hva & Hslots)".
    iDestruct "Hslots" as "(Ht & Hk & Hv & %Lt & %Lk & %Lv & %Hwf)".
    iDestruct (is_array_obj_hm with "Ht") as (ot) "(%Ht & Ht)".
    iDestruct (is_array_obj_hm with "Hk") as (ok) "(%Hk & Hk)".
    iDestruct (is_array_obj_hm with "Hv") as (ov) "(%Hv & Hv)".
    subst a ta ka va sz m.
    assert (0 < cap)%nat as Hcap.
    { destruct (wf_pow _ _ _ _ Hwf) as [e ->]. apply pow_positive. }
    unfold call_probe, probe_for_body, probe_open. hm_pure.
    hm_read. hm_admin. hm_read. hm_admin. hm_read. hm_admin.
    hm_take. iApply (wp_wand with "[Ht]").
    { iApply (array.length_spec with "Ht"). }
    iIntros (r) "[%Hr Ht]". subst r. rewrite Lt. hm_admin.
    try hm_take. iApply (wp_wand with "[]").
    { iApply residue_wp. lia. }
    iIntros (r) "%Hr". subst r. hm_args.
    assert (0 ≤ residue k (Z.of_nat cap))%Z as Hres by
      (pose proof (residue_spec k (Z.of_nat cap) ltac:(lia)); lia).
    replace (residue k (Z.of_nat cap)) with (Z.of_nat (bucket k cap)) by
      (unfold bucket; rewrite Z2Nat.id; lia).
    iApply (wp_wand with "[Ht Hk Hv]").
    { iApply (scan_spec cap (bucket k cap) 0 cap _ _ _ tags keys vals k None with "Ht Hk Hv");
        try done; try (apply bucket_lt; done); lia. }
    iIntros (r) "(%Hr & Ht & Hk & Hv)".
    assert (count_occ tags < cap)%nat as Hcount by
      (pose proof (wf_load _ _ _ _ Hwf); lia).
    pose proof (probe_shape cap tags keys vals k Hcap Lt Lk Lv
      (wf_ok _ _ _ _ Hwf) (wf_dup _ _ _ _ Hwf) (wf_place _ _ _ _ Hwf) Hcount) as Hshape.
    change (r = probe_val (probe cap (bucket k cap) tags keys vals k)) in Hr.
    destruct (probe cap (bucket k cap) tags keys vals k) as [idx v|idx]; simpl in *; subst r.
    - iExists true, idx, v. iSplit; [done|]. iSplit; [done|]. iSplit; [by iPureIntro; discriminate|].
      iExists o, (Z.of_nat (count_occ tags)), (LitV (LitObj ot)), (LitV (LitObj ok)),
        (LitV (LitObj ov)), tags, keys, vals. unfold is_hm_slots. iFrame. repeat iSplit; done.
    - destruct Hshape as (_ & _ & _ & Hnone).
      iExists false, idx, 0%Z. iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
      iExists o, (Z.of_nat (count_occ tags)), (LitV (LitObj ot)), (LitV (LitObj ok)),
        (LitV (LitObj ov)), tags, keys, vals. unfold is_hm_slots. iFrame. repeat iSplit; done.
  Qed.

  Lemma is_hashmap_obj m cap a :
    is_hashmap m cap a -∗ ∃ o, ⌜ a = LitV (LitObj o) ⌝ ∗ is_hashmap m cap a.
  Proof.
    iIntros "Hm". iDestruct "Hm" as (o sz ta ka va tags keys vals) "[%Ha Hrest]".
    iExists o. iSplit; [done|]. iExists o, sz, ta, ka, va, tags, keys, vals.
    iSplit; [done|]. iFrame.
  Qed.

  Lemma contains_spec m cap (a : val_cjr) (k : Z) :
    is_hashmap m cap a -∗
    WP call_contains a k
      {{ v, ⌜ v = LitV (LitBool (bool_decide (is_Some (m !! k)))) ⌝ ∗ is_hashmap m cap a }}.
  Proof.
    iIntros "Hm". iDestruct (is_hashmap_obj with "Hm") as (o) "(%Ha & Hm)". subst a.
    unfold call_contains, contains_body.
    iApply (wp_bind [AppLCtx (Val (StructV [LitV (LitObj o); LitV (LitInt k)]))]).
    iApply wp_rec. iIntros "!> _". iApply wp_app. simpl. hm_admin.
    try hm_take. hm_admin. iApply (wp_wand with "[Hm]").
    { iApply (probe_spec with "Hm"). }
    iIntros (r) "(%found & %idx & %v & %Hr & %Hlookup & %Hzero & Hm)". subst r.
    hm_pure. rewrite Hlookup. destruct found; simpl; iFrame; done.
  Qed.

  Lemma get_spec m cap (a : val_cjr) (k : Z) :
    is_hashmap m cap a -∗
    WP call_get a k
      {{ res, ⌜ res = match m !! k with
                      | Some v => StructV [LitV (LitBool true); LitV (LitInt v)]
                      | None => StructV [LitV (LitBool false); LitV (LitInt 0)]
                      end ⌝ ∗ is_hashmap m cap a }}.
  Proof.
    iIntros "Hm". iDestruct (is_hashmap_obj with "Hm") as (o) "(%Ha & Hm)". subst a.
    unfold call_get, get_body.
    iApply (wp_bind [AppLCtx (Val (StructV [LitV (LitObj o); LitV (LitInt k)]))]).
    iApply wp_rec. iIntros "!> _". iApply wp_app. simpl. hm_admin.
    try hm_take. hm_admin. iApply (wp_wand with "[Hm]").
    { iApply (probe_spec with "Hm"). }
    iIntros (r) "(%found & %idx & %v & %Hr & %Hlookup & %Hzero & Hm)". subst r.
    hm_pure. rewrite Hlookup. destruct found; simpl; iFrame.
    - done.
    - rewrite (Hzero eq_refl). done.
  Qed.

  Lemma grow_spec m cap (a : val_cjr) (minCap : nat) :
    is_hashmap m cap a -∗
    WP call_grow a (Z.of_nat minCap)
      {{ u, ⌜ u = LitV LitUnit ⌝ ∗ is_hashmap m (doubled_cap cap) a }}.
  Proof.
    iIntros "Hm". iDestruct "Hm" as
      (o sz ta ka va tags keys vals) "(%Ha & %Hm & %Hsz & Hsz & Hta & Hka & Hva & Hslots)".
    iDestruct "Hslots" as "(Ht & Hk & Hv & %Lt & %Lk & %Lv & %Hwf)".
    iDestruct (is_array_obj_hm with "Ht") as (ot) "(%Ht & Ht)".
    iDestruct (is_array_obj_hm with "Hk") as (ok) "(%Hk & Hk)".
    iDestruct (is_array_obj_hm with "Hv") as (ov) "(%Hv & Hv)". subst a ta ka va sz m.
    set (nc := doubled_cap cap).
    destruct (wf_pow _ _ _ _ Hwf) as [e Hpow].
    assert (nc = (2 ^ S (S e))%nat) as Hnc by (apply doubled_cap_pow; done).
    assert (0 < nc)%nat as Hpos by (rewrite Hnc; apply pow_positive).
    assert (wf_table nc (replicate nc 0%Z) (replicate nc 0%Z) (replicate nc 0%Z)) as Hempty
      by (apply zeros_wf; eauto).
    unfold call_grow, grow_body. iApply wp_app. simpl. hm_admin.
    hm_read. hm_admin. hm_read. hm_admin. hm_read. hm_admin.
    hm_take. iApply (wp_wand with "[Ht]"). { iApply (array.length_spec with "Ht"). }
    iIntros (r) "[%Hr Ht]". subst r. rewrite Lt. hm_admin.
    replace (Z.of_nat cap + Z.of_nat cap)%Z with (Z.of_nat nc) by (unfold nc, doubled_cap; lia).
    hm_take. iApply (wp_wand with "[]"). { iApply array.make_spec. exact Hpos. }
    iIntros (nta) "Hnt". iDestruct (is_array_obj_hm with "Hnt") as (ont) "(%Hnta & Hnt)". subst nta. hm_admin.
    hm_take. iApply (wp_wand with "[]"). { iApply array.make_spec. exact Hpos. }
    iIntros (nka) "Hnk". iDestruct (is_array_obj_hm with "Hnk") as (onk) "(%Hnka & Hnk)". subst nka. hm_admin.
    hm_take. iApply (wp_wand with "[]"). { iApply array.make_spec. exact Hpos. }
    iIntros (nva) "Hnv". iDestruct (is_array_obj_hm with "Hnv") as (onv) "(%Hnva & Hnv)". subst nva. hm_admin.
    rewrite <- Lt.
    iApply (wp_wand with "[Ht Hk Hv Hnt Hnk Hnv]").
    { iApply (rehash_spec tags keys vals 0 tags keys vals _ _ _ nc _ _ _
        (replicate nc 0%Z) (replicate nc 0%Z) (replicate nc 0%Z)
        with "Ht Hk Hv Hnt Hnk Hnv"); try done.
      - lia.
      - lia.
      - exact (wf_ok _ _ _ _ Hwf).
      - exact (wf_dup _ _ _ _ Hwf).
      - intros x Hin. rewrite contents_zeros. done.
      - rewrite count_zeros. pose proof (wf_load _ _ _ _ Hwf). unfold nc, doubled_cap. lia. }
    iIntros (r) "Harrays".
    destruct (grow_table cap tags keys vals) as [[t2 k2] v2] eqn:Hg.
    assert (rehash_acc nc tags keys vals (replicate nc 0%Z) (replicate nc 0%Z)
      (replicate nc 0%Z) = (t2,k2,v2)) as Hrehash by exact Hg.
    iEval (rewrite Hrehash) in "Harrays".
    iDestruct "Harrays" as "(%Hr & Ht & Hk & Hv & Hnt & Hnk & Hnv)". subst r. hm_admin.
    hm_write. hm_admin. hm_write. hm_admin. hm_write.
    pose proof (grow_table_spec cap tags keys vals e Hpow Hwf) as Hpure.
    rewrite Hg in Hpure. destruct Hpure as [Hwf2 Hcontents].
    assert (count_occ t2 = count_occ tags) as Hcount.
    { pose proof (size_contents tags keys vals ltac:(lia) ltac:(lia) (wf_dup _ _ _ _ Hwf)) as Hold.
      pose proof (size_contents t2 k2 v2
        ltac:(pose proof (wf_tags_len _ _ _ _ Hwf2); pose proof (wf_keys_len _ _ _ _ Hwf2); lia)
        ltac:(pose proof (wf_tags_len _ _ _ _ Hwf2); pose proof (wf_vals_len _ _ _ _ Hwf2); lia)
        (wf_dup _ _ _ _ Hwf2)) as Hnew.
      rewrite Hcontents in Hnew. lia. }
    iSplit; [done|]. iExists o, (Z.of_nat (count_occ tags)), (LitV (LitObj ont)),
      (LitV (LitObj onk)), (LitV (LitObj onv)), t2, k2, v2.
    unfold is_hm_slots. iFrame. repeat iSplit; try done; iPureIntro; first [lia|apply Hwf2].
  Qed.

  Lemma hashmap_bounds m cap a :
    is_hashmap m cap a -∗ ⌜(0 < cap ∧ 2 * size m ≤ cap)%nat⌝ ∗ is_hashmap m cap a.
  Proof.
    iIntros "Hm". iDestruct "Hm" as (o sz ta ka va tags keys vals)
      "(%Ha & %Hm & %Hsz & Hsz & Hta & Hka & Hva & Hslots)".
    iDestruct "Hslots" as "(Ht & Hk & Hv & %Lt & %Lk & %Lv & %Hwf)".
    iSplit.
    - iPureIntro. split; [eapply cap_pos; exact Hwf|]. rewrite <- Hm.
      rewrite (size_contents tags keys vals ltac:(lia) ltac:(lia) (wf_dup _ _ _ _ Hwf)).
      exact (wf_load _ _ _ _ Hwf).
    - iExists o, sz, ta, ka, va, tags, keys, vals. unfold is_hm_slots. iFrame. repeat iSplit; done.
  Qed.

  Lemma add_spec m cap (a : val_cjr) (k v : Z) :
    is_hashmap m cap a -∗
    WP call_add a k v
      {{ u, ⌜ u = LitV LitUnit ⌝ ∗ ∃ cap', is_hashmap (<[k:=v]> m) cap' a }}.
  Proof.
    iIntros "Hm". iDestruct (is_hashmap_obj with "Hm") as (o) "(%Ha & Hm)". subst a.
    iDestruct (hashmap_bounds with "Hm") as "[%Hbounds Hm]".
    destruct Hbounds as [Hcap Hload].
    unfold call_add, add_body. iApply wp_app. simpl. hm_admin.
    iApply (wp_wand with "[Hm]"). { iApply (probe_spec with "Hm"). }
    iIntros (r) "(%found & %idx & %old & %Hr & %Hlookup & %Hzero & Hm)". subst r. hm_admin.
    destruct found.
    - iApply wp_if_true. hm_admin. iApply (wp_wand with "[Hm]").
      { iApply (add_room_spec with "Hm"); [rewrite Hlookup; done|intros Hnone; congruence]. }
      iIntros (r) "[%Hr Hm]". iSplit; [done|]. iExists cap. iFrame.
    - iApply wp_if_false. hm_admin. hm_take.
      iApply (wp_wand with "[Hm]"). { iApply (size_spec with "Hm"). }
      iIntros (r) "[%Hr Hm]". subst r. hm_admin. hm_take.
      iApply (wp_wand with "[Hm]"). { iApply (capacity_spec with "Hm"). }
      iIntros (r) "[%Hr Hm]". subst r. hm_admin.
      destruct (decide (cap ≤ 2 * size m)%nat) as [Hgrow|Hroom].
      + rewrite bool_decide_eq_true_2; [|lia]. iApply wp_if_true. hm_admin.
        replace (Z.of_nat cap + 1)%Z with (Z.of_nat (S cap)) by lia.
        iApply (wp_wand with "[Hm]"). { iApply (grow_spec with "Hm"). }
        iIntros (r) "[%Hr Hm]". subst r. hm_admin.
        iApply (wp_wand with "[Hm]").
        { iApply (add_room_spec with "Hm"); [rewrite Hlookup; done|intros _; unfold doubled_cap; lia]. }
        iIntros (r) "[%Hr Hm]". iSplit; [done|]. iExists (doubled_cap cap). iFrame.
      + rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false. hm_admin.
        iApply (wp_wand with "[Hm]").
        { iApply (add_room_spec with "Hm"); [rewrite Hlookup; done|intros _; lia]. }
        iIntros (r) "[%Hr Hm]". iSplit; [done|]. iExists cap. iFrame.
  Qed.

  Lemma remove_spec m cap (a : val_cjr) (k : Z) :
    is_hashmap m cap a -∗
    WP call_remove a k
      {{ res, ⌜ res = match m !! k with
                      | Some v => LitV (LitInt v)
                      | None => LitV (LitInt 0)
                      end ⌝ ∗ is_hashmap (delete k m) cap a }}.
  Proof.
    iIntros "Hm". iDestruct "Hm" as
      (o sz ta ka va tags keys vals) "(%Ha & %Hm & %Hsz & Hsz & Hta & Hka & Hva & Hslots)".
    iDestruct "Hslots" as "(Ht & Hk & Hv & %Lt & %Lk & %Lv & %Hwf)".
    iDestruct (is_array_obj_hm with "Ht") as (ot) "(%Ht & Ht)".
    iDestruct (is_array_obj_hm with "Hk") as (ok) "(%Hk & Hk)".
    iDestruct (is_array_obj_hm with "Hv") as (ov) "(%Hv & Hv)". subst a ta ka va sz m.
    unfold call_remove, remove_body. iApply wp_app. simpl. hm_admin.
    hm_read. hm_admin. hm_read. hm_admin. hm_read. hm_admin.
    hm_take. iApply (wp_wand with "[Ht]"). { iApply (array.length_spec with "Ht"). }
    iIntros (r) "[%Hr Ht]". subst r. rewrite Lt. hm_admin.
    iApply (wp_wand with "[Ht Hk Hv]").
    { iApply (buffer_probe_spec with "Ht Hk Hv"); try done; eapply cap_pos; exact Hwf. }
    iIntros (r) "(%Hr & Ht & Hk & Hv)". subst r.
    pose proof (probe_slots cap tags keys vals k Hwf) as Hslots.
    pose proof (probe_shape cap tags keys vals k (cap_pos _ _ _ _ Hwf) Lt Lk Lv
      (wf_ok _ _ _ _ Hwf) (wf_dup _ _ _ _ Hwf) (wf_place _ _ _ _ Hwf)
      ltac:(pose proof (wf_load _ _ _ _ Hwf); pose proof (cap_pos _ _ _ _ Hwf); lia)) as Hlookup.
    pose proof (write_remove_spec cap tags keys vals k Hwf) as Hremove.
    unfold write_remove in Hremove.
    destruct (probe cap (bucket k cap) tags keys vals k) as [idx old|idx]; simpl in *.
    - destruct Hslots as (Hi & Htag & Hkey & Hvalue).
      destruct Hremove as [Hwf2 Hcontents].
      hm_admin. iApply wp_if_true. hm_admin. iApply (wp_bind [SeqCtx _]).
      iApply (wp_wand with "[Ht]"). { iApply (arr_set_spec tags _ idx tag_occ tag_tomb Htag with "Ht"). }
      iIntros (r) "[%Hr Ht]". subst r. hm_admin. hm_read. hm_admin.
      hm_write. hm_admin. rewrite Hlookup.
      iSplit; [done|]. iExists o, (Z.of_nat (count_occ tags) - 1)%Z,
        (LitV (LitObj ot)), (LitV (LitObj ok)), (LitV (LitObj ov)), (<[idx:=tag_tomb]> tags), keys, vals.
      unfold is_hm_slots. iFrame. repeat iSplit; try done; iPureIntro;
        first [pose proof (count_bury tags idx Htag); lia|apply Hwf2].
    - destruct Hremove as [Hwf2 Hcontents]. destruct Hlookup as (_ & _ & _ & Hlookup).
      hm_admin. iApply wp_if_false. hm_admin. rewrite Hlookup.
      iSplit; [done|]. iExists o, (Z.of_nat (count_occ tags)), (LitV (LitObj ot)),
        (LitV (LitObj ok)), (LitV (LitObj ov)), tags, keys, vals.
      unfold is_hm_slots. iFrame. repeat iSplit; done.
  Qed.

  Definition size_at (m : expr) : expr :=
    App (Rec None (Some "m") size_body) m.
  Definition capacity_at (m : expr) : expr :=
    App (Rec None (Some "m") capacity_body) m.
  Definition is_empty_at (m : expr) : expr :=
    App (Rec None (Some "m") is_empty_body) m.

  Definition init_then_size : expr :=
    Let (Some "m") call_init (size_at (Var "m")).
  Definition init_then_capacity : expr :=
    Let (Some "m") call_init (capacity_at (Var "m")).
  Definition init_then_empty : expr :=
    Let (Some "m") call_init (is_empty_at (Var "m")).

  Lemma init_then_size_spec :
    ⊢ WP init_then_size
      {{ v, ∃ m, ⌜ v = LitV (LitInt 0) ⌝ ∗ is_hashmap ∅ default_capacity m }}.
  Proof.
    iApply (wp_bind [LetCtx (Some "m") (size_at (Var "m"))]).
    iApply wp_wand. { iApply init_spec. }
    iIntros (m) "Hm". iApply wp_let. simpl.
    iApply (wp_wand with "[Hm]"). { iApply (size_spec with "Hm"). }
    iIntros (v) "[%Hv Hm]". iExists m. iSplit; [done|]. iFrame.
  Qed.

  Lemma init_then_capacity_spec :
    ⊢ WP init_then_capacity
      {{ v, ∃ m, ⌜ v = LitV (LitInt (Z.of_nat default_capacity)) ⌝ ∗
                  is_hashmap ∅ default_capacity m }}.
  Proof.
    iApply (wp_bind [LetCtx (Some "m") (capacity_at (Var "m"))]).
    iApply wp_wand. { iApply init_spec. }
    iIntros (m) "Hm". iApply wp_let. simpl.
    iApply (wp_wand with "[Hm]"). { iApply (capacity_spec with "Hm"). }
    iIntros (v) "[%Hv Hm]". iExists m. iSplit; [done|]. iFrame.
  Qed.

  Lemma init_then_empty_spec :
    ⊢ WP init_then_empty
      {{ v, ∃ m, ⌜ v = LitV (LitBool true) ⌝ ∗ is_hashmap ∅ default_capacity m }}.
  Proof.
    iApply (wp_bind [LetCtx (Some "m") (is_empty_at (Var "m"))]).
    iApply wp_wand. { iApply init_spec. }
    iIntros (m) "Hm". iApply wp_let. simpl.
    iApply (wp_wand with "[Hm]"). { iApply (is_empty_spec with "Hm"). }
    iIntros (v) "[%Hv Hm]". simpl in Hv. iExists m. iSplit; [done|]. iFrame.
  Qed.

  Definition add_then_get (m : val_cjr) (k v : Z) : expr :=
    Let None (call_add m k v) (call_get m k).
  Definition add_then_contains (m : val_cjr) (k v : Z) : expr :=
    Let None (call_add m k v) (call_contains m k).

  Lemma add_then_get_spec m cap (a : val_cjr) (k v : Z) :
    is_hashmap m cap a -∗
    WP add_then_get a k v
      {{ res, ⌜ res = StructV [LitV (LitBool true); LitV (LitInt v)] ⌝ ∗
              (∃ cap', is_hashmap (<[k:=v]> m) cap' a) }}.
  Proof.
    iIntros "Hm". unfold add_then_get.
    iApply (wp_bind [LetCtx None (call_get a k)]).
    iApply (wp_wand with "[Hm]"). { iApply (add_spec with "Hm"). }
    iIntros (u) "[%Hu Hm]". iDestruct "Hm" as (cap') "Hm". subst u.
    iApply wp_let. simpl. iApply (wp_wand with "[Hm]"). { iApply (get_spec with "Hm"). }
    iIntros (r) "[%Hr Hm]". rewrite lookup_insert in Hr. iSplit; [done|]. iExists cap'. iFrame.
  Qed.

  Lemma add_then_contains_spec m cap (a : val_cjr) (k v : Z) :
    is_hashmap m cap a -∗
    WP add_then_contains a k v
      {{ b, ⌜ b = LitV (LitBool true) ⌝ ∗ (∃ cap', is_hashmap (<[k:=v]> m) cap' a) }}.
  Proof.
    iIntros "Hm". unfold add_then_contains.
    iApply (wp_bind [LetCtx None (call_contains a k)]).
    iApply (wp_wand with "[Hm]"). { iApply (add_spec with "Hm"). }
    iIntros (u) "[%Hu Hm]". iDestruct "Hm" as (cap') "Hm". subst u.
    iApply wp_let. simpl. iApply (wp_wand with "[Hm]"). { iApply (contains_spec with "Hm"). }
    iIntros (r) "[%Hr Hm]". rewrite lookup_insert in Hr. simpl in Hr.
    iSplit; [done|]. iExists cap'. iFrame.
  Qed.

End hash_map.
