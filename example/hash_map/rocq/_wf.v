
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
  intros Ht Hold j Hj Heq.
  destruct (decide (i < length tags)%nat) as [Hi|Hi].
  - destruct (decide (probe_slot b j cap = i)) as [->|Hne].
    + rewrite list_lookup_insert in Heq; [|done].
      injection Heq as Heq. apply Ht. exact Heq.
    + rewrite list_lookup_insert_ne in Heq; [|done].
      apply (Hold j Hj). exact Heq.
  - rewrite list_insert_ge in Heq; [|lia].
    apply (Hold j Hj). exact Heq.
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
  - rewrite list_lookup_insert in Hk; [|lia].
    injection Hk as ->.
    intros j Hj.
    assert (probe_slot (bucket k cap) j cap ≠ i) as Hslot.
    { apply path_ne; try done. apply bucket_lt. done. }
    rewrite list_lookup_insert_ne; [|exact Hslot].
    apply Hpath. exact Hj.
  - rewrite list_lookup_insert_ne in Ht; [|exact Hne].
    rewrite list_lookup_insert_ne in Hk; [|exact Hne].
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
    injection Ht as Ht. exfalso. apply tag_tomb_ne_occ. exact Ht.
  - rewrite list_lookup_insert_ne in Ht; [|exact Hne].
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
           apply (IH keys i); [exact Hlen|lia|exact Ht|exact Hin].
      * apply (IH keys i); [exact Hlen|lia|exact Ht|exact Hin].
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
           apply (occ_bury_sub tags keys i k0); [exact Hlen|lia|exact Ht|exact Hin].
        -- apply (IH keys i); [exact Hlen|lia|exact Ht|exact Hdup].
      * apply (IH keys i); [exact Hlen|lia|exact Ht|exact Hdup].
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
    + simpl. rewrite (IH keys vals Hlk Hlv Hdup). lia.
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
  contents_of (replicate n 0) (replicate n 0) (replicate n 0) = ∅.
Proof.
  induction n as [|n IH]; simpl; [done|].
  destruct (decide (0 = tag_occ)) as [Hbad|].
  - unfold tag_occ in Hbad. lia.
  - exact IH.
Qed.

Lemma count_zeros n : count_occ (replicate n 0) = 0%nat.
Proof.
  induction n as [|n IH]; simpl; [done|].
  destruct (decide (0 = tag_occ)) as [Hbad|].
  - unfold tag_occ in Hbad. lia.
  - simpl. exact IH.
Qed.

Lemma occ_zeros n : occ_keys (replicate n 0) (replicate n 0) = [].
Proof.
  induction n as [|n IH]; simpl; [done|].
  destruct (decide (0 = tag_occ)) as [Hbad|].
  - unfold tag_occ in Hbad. lia.
  - exact IH.
Qed.

Lemma tags_ok_zeros n : tags_ok (replicate n 0).
Proof.
  apply Forall_replicate. unfold tag_ok, tag_empty. by left.
Qed.

Lemma placed_zeros cap : placed cap (replicate cap 0) (replicate cap 0).
Proof.
  intros i k Ht _. apply lookup_replicate in Ht as [Ht _].
  unfold tag_occ in Ht. lia.
Qed.

Lemma zeros_wf cap :
  (∃ e, cap = (2 ^ S e)%nat) →
  wf_table cap (replicate cap 0) (replicate cap 0) (replicate cap 0).
Proof.
  intros Hpow. apply (Wf cap (replicate cap 0) (replicate cap 0) (replicate cap 0)).
  - rewrite length_replicate. done.
  - rewrite length_replicate. done.
  - rewrite length_replicate. done.
  - exact Hpow.
  - apply tags_ok_zeros.
  - rewrite occ_zeros. apply NoDup_nil.
  - rewrite count_zeros. lia.
  - apply placed_zeros.
Qed.

Lemma cap_pos cap tags keys vals :
  wf_table cap tags keys vals → (0 < cap)%nat.
Proof.
  intros [???? [e ->] ???]. apply pow_positive.
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
  - rewrite Hr in Hsh. rewrite Hsh in Hnone. discriminate.
  - rewrite Hr in Hsh. destruct Hsh as (Hidx & Htag & Hpath & _).
    assert (tags !! idx ≠ Some tag_occ) as Hnot.
    { destruct Htag as [-> | ->]; intros [=];
        [apply tag_occ_ne_empty|apply tag_tomb_ne_occ]; reflexivity. }
    assert (length keys = length tags) as Hlk by (rewrite Hlkey, Hltag; done).
    assert (length vals = length tags) as Hlv by (rewrite Hlval, Hltag; done).
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
        rewrite Htnone. rewrite lookup_insert. simpl. rewrite lookup_insert. done.
      * rewrite lookup_insert_ne; [|exact Hx].
        simpl. destruct (decide (x = k)); [congruence|]. done.
    + assert (∀ x, x ∈ occ_keys tags keys → contents_of accT accK accV !! x = None)
        as Hdis' by (intros x Hin; apply Hdis; exact Hin).
      assert (2 * (count_occ accT + count_occ tags) ≤ cap)%nat as Hload' by lia.
      specialize (IH keys vals accT accK accV Hwf Hlk Hlv Hok Hdup Hdis' Hload').
      destruct (rehash_acc cap tags keys vals accT accK accV) as [[t2 k2] v2].
      destruct IH as [Hwf' Hlook]. split; [exact Hwf'|].
      intros x. rewrite Hlook. simpl. done.
Qed.
