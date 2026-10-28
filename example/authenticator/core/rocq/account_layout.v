(** Compositional field updates preserve all words outside their slice. *)
From Coq Require Import ZArith List Lia.
From iris.proofmode Require Import proofmode.
From cjr.authenticator Require Import accounts account_model memory_application.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.
Lemma slice_write_embedded (prefix block suffix replacement : list Z) offset :
 (offset+length replacement <= length block)%nat ->
 slice_write (prefix++block++suffix) (length prefix+offset) replacement =
 prefix ++ slice_write block offset replacement ++ suffix.
Proof.
 intros Hbounds. unfold slice_write.
 rewrite take_app_add take_app_le; [|lia].
 replace (length prefix+offset+length replacement)%nat with
   (length prefix+(offset+length replacement))%nat by lia.
 rewrite drop_app_add drop_app_le; [|exact Hbounds].
 rewrite !app_assoc. reflexivity.
Qed.
Lemma insert_embedded (prefix block suffix : list Z) i x : (i < length block)%nat ->
 <[(length prefix+i)%nat := x]> (prefix++block++suffix) =
 prefix ++ <[i := x]> block ++ suffix.
Proof.
 intros Hi. rewrite insert_app_r_alt; [|lia].
 replace (length prefix+i-length prefix)%nat with i by lia.
 rewrite insert_app_l; [reflexivity|exact Hi].
Qed.
Lemma slice_write_exact (prefix block suffix replacement : list Z) :
 length replacement = length block ->
 slice_write (prefix++block++suffix) (length prefix) replacement = prefix++replacement++suffix.
Proof.
 intros Hlen. unfold slice_write. rewrite take_app_length.
 rewrite Hlen drop_app_add drop_app_length. reflexivity.
Qed.
Lemma replicate_repeat {A} n (x : A) : replicate n x = repeat x n.
Proof. induction n; simpl; [reflexivity|rewrite IHn; reflexivity]. Qed.
Lemma padded_zero_write xs : (length xs <= 128)%nat ->
 slice_write (replicate 128 0%Z) 0 xs = padded_field xs.
Proof.
 intros Hlen. unfold slice_write,padded_field. simpl take.
 rewrite Nat.add_0_l drop_replicate replicate_repeat. reflexivity.
Qed.
Lemma zeroed_metadata_fields label issuer :
 (length label <= 128)%nat -> (length issuer <= 128)%nat ->
 slice_write (slice_write (replicate 256 0%Z) 0 label) 128 issuer =
 padded_field label ++ padded_field issuer.
Proof.
 intros Hl Hi.
 change (replicate 256 0%Z) with (replicate (128+128) 0%Z).
 rewrite replicate_add.
 pose proof (slice_write_embedded [] (replicate 128 0%Z) (replicate 128 0%Z) label 0) as Hlabel.
 cbn [app length] in Hlabel. rewrite length_replicate in Hlabel.
 rewrite Hlabel; [|exact Hl]. rewrite padded_zero_write; [|exact Hl].
 replace 128%nat with (length (padded_field label)+0)%nat at 2 by (rewrite padded_field_length; lia).
 pose proof (slice_write_embedded (padded_field label) (replicate 128 0%Z) [] issuer 0) as Hissuer.
 rewrite app_nil_r in Hissuer. rewrite Hissuer; [|rewrite length_replicate; lia].
 rewrite padded_zero_write; [rewrite app_nil_r; reflexivity|exact Hi].
Qed.
Definition rename_slot_words words label issuer :=
 <[4%nat := Z.of_nat (length issuer)]>
 (<[3%nat := Z.of_nat (length label)]>
  (slice_write (slice_write (slice_write words 6 (replicate 256 0%Z)) 6 label) 134 issuer)).
Lemma rename_slot_words_length words label issuer :
 (390 <= length words)%nat -> (length label <=128)%nat -> (length issuer<=128)%nat ->
 length (rename_slot_words words label issuer) = length words.
Proof.
 intros Hwords Hl Hi. unfold rename_slot_words. rewrite !length_insert.
 rewrite !slice_write_length; rewrite ?length_replicate; lia.
Qed.
Lemma rename_slot_words_canonical a label issuer : account_valid a ->
 (length label <=128)%nat -> (length issuer<=128)%nat ->
 rename_slot_words (slot_words (Some a)) label issuer = slot_words (Some (with_metadata a label issuer)).
Proof.
 intros Ha Hl Hi. destruct Ha as [Hid [Hlabel [Hissuer [Hsecret Hrest]]]].
 set (header := [account_id a;account_digits a;account_period a;
   Z.of_nat (length (account_label a));Z.of_nat (length (account_issuer a));Z.of_nat (length (account_secret a))]).
 assert (Hheader : length header = 6%nat) by reflexivity.
 assert (Hfields : length (padded_field (account_label a) ++ padded_field (account_issuer a)) = 256%nat).
 { rewrite length_app !padded_field_length; lia. }
 assert (Hlayout : header ++ padded_field (account_label a) ++ padded_field (account_issuer a) ++ padded_field (account_secret a) =
   header ++ (padded_field (account_label a) ++ padded_field (account_issuer a)) ++ padded_field (account_secret a)).
 { rewrite !app_assoc. reflexivity. }
 change (rename_slot_words
   (header ++ padded_field (account_label a) ++ padded_field (account_issuer a) ++ padded_field (account_secret a))
   label issuer = slot_words (Some (with_metadata a label issuer))).
 unfold rename_slot_words. rewrite Hlayout.
 replace 6%nat with (length header) at 1 by reflexivity.
 rewrite slice_write_exact; [|rewrite length_replicate; symmetry; exact Hfields].
 replace 6%nat with (length header+0)%nat by reflexivity.
 rewrite slice_write_embedded; [|rewrite length_replicate; lia].
 replace 134%nat with (length header+128)%nat by reflexivity.
 rewrite slice_write_embedded; [|rewrite slice_write_length; rewrite ?length_replicate; lia].
 rewrite zeroed_metadata_fields; [|exact Hl|exact Hi].
 rewrite !insert_app_l; try (rewrite ?length_insert Hheader; lia).
 unfold header. simpl. rewrite !app_assoc. reflexivity.
Qed.
