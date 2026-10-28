(** Filling a zeroed vacant slot refines abstract enrollment. *)
From Coq Require Import ZArith List Lia.
From iris.proofmode Require Import proofmode.
From cjr.authenticator Require Import accounts account_model account_representation account_layout
 account_rename_representation memory_application sessions account_slots account_enroll.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.
Lemma zeroed_account_fields label issuer secret :
 (length label<=128)%nat -> (length issuer<=128)%nat -> (length secret<=128)%nat ->
 slice_write (slice_write (slice_write (replicate 384 0%Z) 0 label) 128 issuer) 256 secret =
 padded_field label ++ padded_field issuer ++ padded_field secret.
Proof.
 intros Hl Hi Hs.
 change (replicate 384 0%Z) with (replicate (256+128) 0%Z). rewrite replicate_add.
 pose proof (slice_write_embedded [] (replicate 256 0%Z) (replicate 128 0%Z) label 0) as Hlabel.
 cbn [app length] in Hlabel. rewrite length_replicate in Hlabel.
 rewrite Hlabel; [|lia].
 pose proof (slice_write_embedded [] (slice_write (replicate 256 0%Z) 0 label) (replicate 128 0%Z) issuer 128) as Hissuer.
 cbn [app length] in Hissuer. rewrite Hissuer; [|rewrite slice_write_length; rewrite ?length_replicate; lia].
 rewrite zeroed_metadata_fields; [|exact Hl|exact Hi].
 replace 256%nat with (length (padded_field label ++ padded_field issuer)+0)%nat at 1
   by (rewrite length_app !padded_field_length; lia).
 pose proof (slice_write_embedded (padded_field label ++ padded_field issuer) (replicate 128 0%Z) [] secret 0) as Hsecret.
 rewrite app_nil_r in Hsecret. rewrite Hsecret; [|rewrite length_replicate; lia].
 rewrite padded_zero_write; [|exact Hs]. rewrite app_nil_r app_assoc. reflexivity.
Qed.
Definition enroll_slot_words words id label issuer secret digits period :=
 let metadata := <[5%nat := Z.of_nat (length secret)]>
  (<[4%nat := Z.of_nat (length issuer)]> (<[3%nat := Z.of_nat (length label)]>
  (<[2%nat := period]> (<[1%nat := digits]> (<[0%nat := id]> words))))) in
 slice_write (slice_write (slice_write metadata 6 label) 134 issuer) 262 secret.
Lemma enroll_slot_words_canonical id label issuer secret digits period :
 (length label<=128)%nat -> (length issuer<=128)%nat -> (length secret<=128)%nat ->
 enroll_slot_words (slot_words None) id label issuer secret digits period =
 slot_words (Some (Account id label issuer secret digits period)).
Proof.
 intros Hl Hi Hs. unfold enroll_slot_words. cbn zeta.
 set (header := [id;digits;period;Z.of_nat (length label);Z.of_nat (length issuer);Z.of_nat (length secret)]).
 change (slice_write (slice_write (slice_write (header++replicate 384 0%Z) 6 label) 134 issuer) 262 secret =
   slot_words (Some (Account id label issuer secret digits period))).
 assert (Hheader : length header = 6%nat) by reflexivity.
 replace (header++replicate 384 0%Z) with (header++replicate 384 0%Z++[]) by (rewrite app_nil_r; reflexivity).
 replace 6%nat with (length header+0)%nat by reflexivity.
 rewrite slice_write_embedded; [|rewrite length_replicate; lia].
 replace 134%nat with (length header+128)%nat by reflexivity.
 rewrite slice_write_embedded; [|rewrite slice_write_length; rewrite ?length_replicate; lia].
 replace 262%nat with (length header+256)%nat by reflexivity.
 rewrite slice_write_embedded; [|rewrite !slice_write_length; rewrite ?length_replicate; lia].
 rewrite zeroed_account_fields; [|exact Hl|exact Hi|exact Hs].
 rewrite app_nil_r. unfold header. cbn [slot_words account_label account_issuer account_secret account_id account_digits account_period].
 rewrite !app_assoc. reflexivity.
Qed.
Lemma enroll_embedded prefix block suffix id label issuer secret digits period :
 length block = 390%nat -> (length label<=128)%nat -> (length issuer<=128)%nat -> (length secret<=128)%nat ->
 let metadata :=
  <[(length prefix+5)%nat := Z.of_nat (length secret)]>
  (<[(length prefix+4)%nat := Z.of_nat (length issuer)]>
  (<[(length prefix+3)%nat := Z.of_nat (length label)]>
  (<[(length prefix+2)%nat := period]>
  (<[(length prefix+1)%nat := digits]>
  (<[(length prefix+0)%nat := id]> (prefix++block++suffix)))))) in
 slice_write (slice_write (slice_write metadata (length prefix+6) label)
   (length prefix+134) issuer) (length prefix+262) secret =
 prefix ++ enroll_slot_words block id label issuer secret digits period ++ suffix.
Proof.
 intros Hblock Hl Hi Hs. cbn zeta.
 do 6 (rewrite insert_embedded; [|rewrite ?length_insert Hblock; lia]).
 assert (Hmetadata : length (<[5%nat:=Z.of_nat (length secret)]>
  (<[4%nat:=Z.of_nat (length issuer)]> (<[3%nat:=Z.of_nat (length label)]>
  (<[2%nat:=period]> (<[1%nat:=digits]> (<[0%nat:=id]> block)))))) = 390%nat).
 { rewrite !length_insert. exact Hblock. }
 rewrite slice_write_embedded; [|lia].
 rewrite slice_write_embedded; [|rewrite slice_write_length; lia].
 rewrite slice_write_embedded; [|rewrite !slice_write_length; lia].
 reflexivity.
Qed.
Lemma slot_accounts_fill_length slots i a : slots !! i = Some None ->
 length (slot_accounts (<[i := Some a]> slots)) = S (length (slot_accounts slots)).
Proof.
 revert slots. induction i; intros [|entry slots] Hlookup; simpl in Hlookup; try discriminate.
 - inversion Hlookup; subst entry. reflexivity.
 - destruct entry; simpl; specialize (IHi _ Hlookup); lia.
Qed.
Lemma encoding_fill_empty next slots i a : slots !! i = Some None ->
 session_encoding (next+1) (<[i := Some a]> slots) =
 ([next+1; Z.of_nat (length (slot_accounts slots))+1] ++ flat_map slot_words (take i slots)) ++
 slot_words (Some a) ++ flat_map slot_words (drop (S i) slots).
Proof.
 intros Hlookup. unfold session_encoding.
 rewrite (slot_accounts_fill_length _ _ a Hlookup) Nat2Z.inj_succ.
 rewrite insert_take_drop; [|eapply lookup_lt_Some; eauto].
 rewrite flat_map_app. cbn [flat_map]. rewrite !app_assoc. reflexivity.
Qed.
Lemma enrolled_encoding_empty next slots i label issuer secret digits period :
 Forall valid_slot slots -> slots !! i = Some None ->
 (length label<=128)%nat -> (length issuer<=128)%nat -> (length secret<=128)%nat ->
 enrolled_words (session_encoding next slots) i label issuer secret digits period =
 session_encoding (next+1) (<[i := Some (Account next label issuer secret digits period)]> slots).
Proof.
 intros Hvalid Hlookup Hl Hi Hs. unfold enrolled_words.
 assert (Hid : default 0 (session_encoding next slots !! 0%nat) = next) by reflexivity.
 assert (Hcount : default 0 (session_encoding next slots !! 1%nat) = Z.of_nat (length (slot_accounts slots))) by reflexivity.
 rewrite Hid Hcount. cbn zeta.
 rewrite (encoding_slot_decompose next slots i None Hlookup).
 set (prefix := [next;Z.of_nat (length (slot_accounts slots))] ++ flat_map slot_words (take i slots)).
 assert (Hprefix : length prefix = (2+390*i)%nat).
 { unfold prefix. rewrite length_app encoded_slots_length; [rewrite length_take; simpl; pose proof (lookup_lt_Some _ _ _ Hlookup); lia|].
   apply Forall_take. exact Hvalid. }
 rewrite <- Hprefix. rewrite enroll_embedded; [|reflexivity|exact Hl|exact Hi|exact Hs].
 rewrite enroll_slot_words_canonical; [|exact Hl|exact Hi|exact Hs].
 unfold prefix.
 change (([next+1;Z.of_nat (length (slot_accounts slots))+1] ++ flat_map slot_words (take i slots)) ++
   slot_words (Some (Account next label issuer secret digits period)) ++ flat_map slot_words (drop (S i) slots) =
   session_encoding (next+1) (<[i := Some (Account next label issuer secret digits period)]> slots)).
 symmetry. apply encoding_fill_empty. exact Hlookup.
Qed.
Lemma vacant_slot_exists slots : (length (slot_accounts slots) < length slots)%nat ->
 exists i, slots !! i = Some None.
Proof.
 induction slots as [|entry slots IH]; simpl; [lia|].
 destruct entry as [a|]; simpl.
 - intros Hlen. destruct (IH ltac:(lia)) as [i Hi]. exists (S i). exact Hi.
 - intros _. exists 0%nat. reflexivity.
Qed.
Lemma first_free_encoded next slots : Forall valid_slot slots ->
 (length (slot_accounts slots) < length slots)%nat ->
 exists i, first_free_slot (session_encoding next slots) (length slots) = Z.of_nat i /\ slots !! i = Some None.
Proof.
 intros Hvalid Hroom. destruct (vacant_slot_exists _ Hroom) as [i Hi].
 assert (Hex : exists j, (j<length slots)%nat /\ slot_identifier (session_encoding next slots) j = 0).
 { exists i. split; [eapply lookup_lt_Some; eauto|].
   rewrite (encoded_identifier_lookup _ _ _ _ Hvalid Hi). reflexivity. }
 pose proof (first_free_slot_exists _ _ Hex) as Hfound.
 set (index := Z.to_nat (first_free_slot (session_encoding next slots) (length slots))).
 assert (Hindex : (index<length slots)%nat) by (unfold index; lia).
 destruct (lookup_lt_is_Some_2 slots index Hindex) as [entry Hentry].
 exists index. split; [unfold index; lia|].
 pose proof (first_free_slot_vacant (session_encoding next slots) (length slots) ltac:(lia)) as Hzero.
 fold index in Hzero. rewrite (encoded_identifier_lookup _ _ _ _ Hvalid Hentry) in Hzero.
 destruct entry as [a|]; [|exact Hentry].
 pose proof (proj1 (Forall_lookup _ _) Hvalid index (Some a) Hentry) as Ha.
 unfold valid_slot,account_valid in Ha. simpl in Hzero. lia.
Qed.
Theorem enrolled_words_represents words s label issuer secret digits period :
 session_valid s -> represents_session words s ->
 valid_input label issuer secret digits period = true ->
 (length (accounts s) < 16)%nat -> next_id s <= 9223372036854775806 ->
 represents_session
   (enrolled_words words (Z.to_nat (first_free_slot words 16)) label issuer secret digits period)
   (snd (enroll s label issuer secret digits period)).
Proof.
 intros Hsession [slots [Hlen [Hvalid [Hperm ->]]]] Hinput Hroom Hnext.
 assert (Hslotroom : (length (slot_accounts slots)<length slots)%nat).
 { rewrite Hlen (Permutation_length Hperm). exact Hroom. }
 destruct (first_free_encoded (next_id s) slots Hvalid Hslotroom) as [i [Hfree Hlookup]].
 assert (Hfree16 : first_free_slot (session_encoding (next_id s) slots) 16 = Z.of_nat i).
 { rewrite <- Hlen. exact Hfree. }
 rewrite Hfree16 Nat2Z.id.
 assert (Ha : account_valid (Account (next_id s) label issuer secret digits period)).
 { apply valid_input_spec; [exact Hinput|destruct Hsession as [_ [Hpositive _]]; lia]. }
 pose proof Ha as Hfields. destruct Hfields as [_ [Hl [Hi [Hs Hrest]]]].
 cbn [account_label account_issuer account_secret] in Hl, Hi, Hs.
 rewrite (enrolled_encoding_empty (next_id s) slots i label issuer secret digits period Hvalid Hlookup ltac:(lia) Hi ltac:(lia)).
 unfold enroll. rewrite Hinput (proj2 (Nat.ltb_lt _ _) Hroom) (proj2 (Z.leb_le _ _) Hnext).
 simpl snd. apply enroll_slot_represents; assumption.
Qed.
