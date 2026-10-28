(** CJR big-endian byte output shared by hashing and counter encoding. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.
Definition encoded_byte width x i := Z.rem (Z.quot x (256 ^ Z.of_nat (width-1-i))) 256.
Definition encoding_steps p start width x indices :=
 map (fun i => put (pv p) (add (int (Z.of_nat start)) (int (Z.of_nat i)))
   (rem (div (int x) (int (256 ^ Z.of_nat (width-1-i)))) (int 256))) indices.
Definition encoding_updates start width x indices (words : list Z) :=
 fold_left (fun words i => <[(start+i)%nat := encoded_byte width x i]> words) indices words.
Lemma encoding_updates_length start width x indices words :
 length (encoding_updates start width x indices words) = length words.
Proof.
 unfold encoding_updates. revert words. induction indices as [|i indices IH]; intros words; simpl.
 - done.
 - rewrite IH length_insert. done.
Qed.
Lemma encoded_byte_lookup width x i : (i < width)%nat ->
 model.be_bytes width x !! i = Some (encoded_byte width x i).
Proof.
 intros Hi. unfold model.be_bytes.
 change ((encoded_byte width x <$> seq 0 width) !! i = Some (encoded_byte width x i)).
 rewrite list_lookup_fmap (lookup_seq_lt 0 width i Hi). reflexivity.
Qed.
Lemma encoding_updates_snoc start width x indices i words :
 encoding_updates start width x (indices ++ [i]) words =
 <[(start+i)%nat := encoded_byte width x i]> (encoding_updates start width x indices words).
Proof. unfold encoding_updates. rewrite fold_left_app. reflexivity. Qed.
Lemma encoding_prefix_write (prefix words : list Z) x :
 (length prefix < length words)%nat ->
 <[length prefix := x]> (prefix ++ drop (length prefix) words) =
 (prefix ++ [x]) ++ drop (S (length prefix)) words.
Proof.
 intros Hlen. destruct (lookup_lt_is_Some_2 words (length prefix) Hlen) as [old Hold].
 rewrite (drop_S words old (length prefix) Hold) insert_app_r_alt; last lia.
 rewrite Nat.sub_diag. simpl. rewrite <- app_assoc. done.
Qed.
Lemma encoding_updates_prefix start width x words k :
 (k <= width)%nat -> (start+k <= length words)%nat ->
 encoding_updates start width x (seq 0 k) words =
 (take start words ++ take k (model.be_bytes width x)) ++ drop (start+k) words.
Proof.
 induction k as [|k IH]; intros Hwidth Hwords.
 - unfold encoding_updates. simpl. rewrite app_nil_r Nat.add_0_r take_drop. done.
 - rewrite seq_S encoding_updates_snoc.
   rewrite (IH ltac:(lia) ltac:(lia)).
   set (prefix := take start words ++ take k (model.be_bytes width x)).
   assert (Hprefix : length prefix = (start+k)%nat).
   { unfold prefix. rewrite length_app !length_take model.be_bytes_length.
     rewrite !Nat.min_l; lia. }
   assert (Hcap : (length prefix < length words)%nat) by lia.
   rewrite Nat.add_0_l. rewrite <- Hprefix at 1 2. rewrite (encoding_prefix_write prefix words _ Hcap).
   rewrite (take_S_r (model.be_bytes width x) k (encoded_byte width x k)
     (encoded_byte_lookup width x k ltac:(lia))).
   replace (start+S k)%nat with (S (length prefix)) by lia.
   unfold prefix. rewrite app_assoc. done.
Qed.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem encoding_steps_wp p words start width x indices :
 Forall (fun i => (start+i < length words)%nat) indices ->
 array.array_cells p words -∗
 WP seqs (encoding_steps p start width x indices) unit_e
 {{u, ⌜u = LitV LitUnit⌝ ∗
   array.array_cells p (encoding_updates start width x indices words)}}.
Proof.
 revert words. induction indices as [|i indices IH]; intros words Hbounds.
 - iIntros "Hwords". simpl. iApply wp_value'. iFrame. done.
 - inversion Hbounds as [|? ? Hi Hrest]; subst.
   iIntros "Hwords". cbn [encoding_steps seqs map fold_right].
   iApply (wp_bind [SeqCtx (seqs (encoding_steps p start width x indices) unit_e)]).
   unfold put, ptr, pv, add, rem, div, int, op. auth_pure.
   destruct (lookup_lt_is_Some_2 words (start+i)%nat Hi) as [old Hold].
   iDestruct (big_sepL_insert_acc with "Hwords") as "[Hcell Hclose]"; [exact Hold|].
   rewrite Nat2Z.inj_add. iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
   iDestruct ("Hclose" $! (encoded_byte width x i) with "Hcell") as "Hwords".
   iApply wp_seq. iApply (IH with "Hwords").
   rewrite Forall_forall in Hrest. rewrite Forall_forall.
   intros j Hj. rewrite length_insert. apply Hrest. exact Hj.
Qed.
Theorem emit_be_wp p words start x width :
 (start+width <= length words)%nat ->
 array.array_cells p words -∗
 WP emit_be (pv p) (int (Z.of_nat start)) (int x) width
 {{u, ⌜u = LitV LitUnit⌝ ∗ array.array_cells p
   ((take start words ++ model.be_bytes width x) ++ drop (start+width) words)}}.
Proof.
 intros Hbounds. iIntros "Hwords".
 iApply (wp_wand with "[Hwords]").
 { iApply (encoding_steps_wp p words start width x (seq 0 width) with "Hwords").
   rewrite Forall_forall. intros i Hi. apply elem_of_seq in Hi. lia. }
 iIntros (u) "[%Hu Hwords]".
 rewrite encoding_updates_prefix; [|lia|exact Hbounds].
 rewrite (take_ge (model.be_bytes width x) width); last (rewrite model.be_bytes_length; lia).
 iFrame. done.
Qed.
End proofs.
