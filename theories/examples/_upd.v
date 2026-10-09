
(** * Insertion, deletion, and growth *)

Lemma tag_occ_ne_empty : tag_occ ≠ tag_empty.
Proof. unfold tag_occ, tag_empty. lia. Qed.

Lemma tag_tomb_ne_empty : tag_tomb ≠ tag_empty.
Proof. unfold tag_tomb, tag_empty. lia. Qed.

Lemma tag_tomb_ne_occ : tag_tomb ≠ tag_occ.
Proof. unfold tag_tomb, tag_occ. lia. Qed.

Lemma room_for_one cap n :
  (∃ e, cap = (2 ^ S e)%nat) →
  (2 * n < cap)%nat →
  (2 * S n ≤ cap)%nat.
Proof.
  intros [e ->] Hlt. simpl. lia.
Qed.

Lemma double_pow e : (2 ^ S e + 2 ^ S e = 2 ^ S (S e))%nat.
Proof. simpl. lia. Qed.

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
        simpl. rewrite (IH keys vals i Hlk Hlv ltac:(lia) Hne Hnin).
        rewrite insert_commute; [reflexivity|exact Hkk0].
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
      rewrite delete_insert.
      apply delete_notin.
      apply (contents_none_iff tags keys vals k Hlk Hlv). exact Hnin.
    + simpl in Ht, Hk, Hv, Hdup. simpl.
      destruct (decide (t = tag_occ)) as [->|Hnot].
      * simpl in Hdup. apply NoDup_cons in Hdup as [Hnin Hdup].
        assert (k0 ≠ k) as Hne.
        { intros ->. apply Hnin. eapply occ_in; eauto. }
        simpl. rewrite (IH keys vals i k v Hlk Hlv Hdup Ht Hk Hv).
        rewrite delete_insert_ne; [reflexivity|exact Hne].
      * simpl. apply (IH keys vals i k v Hlk Hlv Hdup Ht Hk Hv).
Qed.
