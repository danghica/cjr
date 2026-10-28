(** Exact metadata writes refine the abstract rename operation. *)
From Coq Require Import ZArith List Lia.
From iris.proofmode Require Import proofmode.
From cjr.authenticator Require Import accounts account_model account_representation account_layout
 memory_application sessions account_rename.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.
Lemma slot_accounts_some_length slots i a b : slots !! i = Some (Some a) ->
 length (slot_accounts (<[i := Some b]> slots)) = length (slot_accounts slots).
Proof.
 revert slots. induction i; intros [|entry slots] Hlookup; simpl in Hlookup; try discriminate.
 - inversion Hlookup; subst entry. reflexivity.
 - destruct entry; simpl; specialize (IHi _ Hlookup); lia.
Qed.
Lemma encoding_slot_decompose next slots i old : slots !! i = Some old ->
 session_encoding next slots =
 ([next;Z.of_nat (length (slot_accounts slots))] ++ flat_map slot_words (take i slots)) ++
 slot_words old ++ flat_map slot_words (drop (S i) slots).
Proof.
 intros Hlookup.
 pose proof (f_equal (flat_map slot_words) (take_drop_middle slots i old Hlookup)) as Hflat.
 rewrite flat_map_app in Hflat. cbn [flat_map] in Hflat.
 unfold session_encoding. rewrite <- Hflat. rewrite !app_assoc. reflexivity.
Qed.
Lemma encoding_replace_some next slots i a b : slots !! i = Some (Some a) ->
 session_encoding next (<[i := Some b]> slots) =
 ([next;Z.of_nat (length (slot_accounts slots))] ++ flat_map slot_words (take i slots)) ++
 slot_words (Some b) ++ flat_map slot_words (drop (S i) slots).
Proof.
 intros Hlookup. unfold session_encoding.
 rewrite (slot_accounts_some_length _ _ _ _ Hlookup).
 rewrite insert_take_drop; [|eapply lookup_lt_Some; eauto].
 rewrite flat_map_app. cbn [flat_map]. rewrite !app_assoc. reflexivity.
Qed.
Lemma rename_embedded prefix block suffix label issuer :
 length block = 390%nat -> (length label<=128)%nat -> (length issuer<=128)%nat ->
 <[(length prefix+4)%nat := Z.of_nat (length issuer)]>
 (<[(length prefix+3)%nat := Z.of_nat (length label)]>
 (slice_write (slice_write
   (slice_write (prefix++block++suffix) (length prefix+6) (replicate 256 0%Z))
   (length prefix+6) label) (length prefix+134) issuer)) =
 prefix ++ rename_slot_words block label issuer ++ suffix.
Proof.
 intros Hblock Hl Hi.
 assert (Hw : length (slice_write block 6 (replicate 256 0%Z)) = 390%nat).
 { rewrite slice_write_length; rewrite ?length_replicate; lia. }
 assert (Hlabeled : length (slice_write (slice_write block 6 (replicate 256 0%Z)) 6 label) = 390%nat).
 { rewrite slice_write_length; lia. }
 assert (Hissued : length (slice_write (slice_write (slice_write block 6 (replicate 256 0%Z)) 6 label) 134 issuer) = 390%nat).
 { rewrite slice_write_length; lia. }
 rewrite (slice_write_embedded prefix block suffix (replicate 256 0%Z) 6); [|rewrite length_replicate; lia].
 rewrite slice_write_embedded; [|lia]. rewrite slice_write_embedded; [|lia].
 rewrite insert_embedded; [|lia]. rewrite insert_embedded; [|rewrite length_insert; lia].
 reflexivity.
Qed.
Lemma renamed_encoding_present next slots id i a label issuer :
 length slots = 16%nat -> Forall valid_slot slots -> slots !! i = Some (Some a) ->
 scan_identifiers (session_encoding next slots) id (length slots) = Z.of_nat i ->
 (length label <=128)%nat -> (length issuer<=128)%nat ->
 renamed_words (session_encoding next slots) id label issuer =
 session_encoding next (<[i := Some (with_metadata a label issuer)]> slots).
Proof.
 intros Hlen Hvalid Hlookup Hscan Hl Hi.
 assert (Hscan16 : scan_identifiers (session_encoding next slots) id 16 = Z.of_nat i).
 { rewrite <- Hlen. exact Hscan. }
 unfold renamed_words. rewrite Hscan16 bool_decide_true; [|lia]. rewrite Nat2Z.id. cbn zeta.
 rewrite (encoding_slot_decompose next slots i (Some a) Hlookup).
 set (prefix := [next;Z.of_nat (length (slot_accounts slots))] ++ flat_map slot_words (take i slots)).
 assert (Hprefix : length prefix = (2+390*i)%nat).
 { unfold prefix. rewrite length_app encoded_slots_length; [rewrite length_take; simpl; pose proof (lookup_lt_Some _ _ _ Hlookup); lia|].
   apply Forall_take. exact Hvalid. }
 rewrite <- Hprefix.
 rewrite rename_embedded.
 - rewrite (rename_slot_words_canonical a label issuer).
   + symmetry. apply (encoding_replace_some next slots i a (with_metadata a label issuer) Hlookup).
   + apply (proj1 (Forall_lookup _ _) Hvalid i (Some a) Hlookup).
   + exact Hl.
   + exact Hi.
 - apply slot_words_length. apply (proj1 (Forall_lookup _ _) Hvalid i (Some a) Hlookup).
 - exact Hl.
 - exact Hi.
Qed.
Lemma find_account_present s a : In a (accounts s) ->
 exists found, find_account s (account_id a) = Some found.
Proof.
 unfold find_account. induction (accounts s) as [|b xs IH]; simpl; [contradiction|].
 destruct (account_id b =? account_id a)%Z eqn:Hb.
 - intros _. eauto.
 - intros [<-|Hin]; [rewrite Z.eqb_refl in Hb; discriminate|auto].
Qed.
Lemma find_account_absent s id :
 (forall a, In a (accounts s) -> account_id a <> id) -> find_account s id = None.
Proof.
 unfold find_account. induction (accounts s) as [|a xs IH]; intros Hnone; simpl; [reflexivity|].
 rewrite (proj2 (Z.eqb_neq _ _) (Hnone a (or_introl eq_refl))).
 apply IH. intros b Hb. apply Hnone. right. exact Hb.
Qed.
Theorem renamed_words_refines words s id label issuer :
 session_valid s -> represents_session words s -> metadata_valid label issuer ->
 fst (rename_account s id label issuer) = bool_decide (0 <= scan_identifiers words id 16) /\
 represents_session (renamed_words words id label issuer) (snd (rename_account s id label issuer)).
Proof.
 intros Hsession [slots [Hlen [Hvalid [Hperm ->]]]] Hmetadata.
 assert (Hmetab : metadata_validb label issuer = true) by (apply metadata_validb_spec; exact Hmetadata).
 destruct Hmetadata as [Hlabel [Hissuer Hbytes]].
 destruct (scan_identifiers_range (session_encoding (next_id s) slots) id 16) as [Habs|Hfound].
 - assert (Hnone : find_account s id = None).
   { apply find_account_absent. intros a Hin.
     apply (scan_encoded_absent (next_id s) slots id Hvalid).
     - rewrite Hlen. exact Habs.
     - eapply Permutation_in; [symmetry; exact Hperm|exact Hin]. }
   unfold rename_account. rewrite Hmetab Hnone. simpl fst. simpl snd.
   rewrite Habs. split; [rewrite bool_decide_false; [reflexivity|lia]|].
   unfold renamed_words. rewrite Habs. simpl. exists slots. auto.
 - assert (Hfound' : 0 <= scan_identifiers (session_encoding (next_id s) slots) id (length slots)).
   { rewrite Hlen. lia. }
   destruct (scan_encoded_present _ _ _ Hvalid Hfound') as [i [a [Hlookup [Hscan Hid]]]].
   assert (Hin : In a (accounts s)).
   { eapply Permutation_in; [exact Hperm|]. eapply slot_account_member; eauto. }
   destruct (find_account_present s a Hin) as [found Hfind]. rewrite Hid in Hfind.
   unfold rename_account. rewrite Hmetab Hfind. simpl fst. simpl snd.
   split; [rewrite bool_decide_true; [reflexivity|lia]|].
   rewrite (renamed_encoding_present (next_id s) slots id i a label issuer Hlen Hvalid Hlookup Hscan ltac:(lia) Hissuer).
   rewrite <- Hid. apply rename_slot_represents; auto.
   unfold metadata_valid. repeat split; tauto.
Qed.
Corollary renamed_words_represents words s id label issuer success s' :
 session_valid s -> represents_session words s -> metadata_valid label issuer ->
 rename_account s id label issuer = (success,s') ->
 session_valid s' /\ represents_session (renamed_words words id label issuer) s'.
Proof.
 intros Hsession Hwords Hmetadata Hrename. split.
 - eapply rename_preserves_validity; eauto.
 - pose proof (proj2 (renamed_words_refines words s id label issuer Hsession Hwords Hmetadata)) as Hrep.
   rewrite Hrename in Hrep. exact Hrep.
Qed.
