(** Public application-port contracts over the abstract session model. *)
From Coq Require Import ZArith String List Lia Bool.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.authenticator Require Import model program refinement memory memory_application sessions
 accounts account_model account_refinement account_rename account_representation account_layout
 account_rename_representation account_enroll_representation account_code input_memory
 account_enroll_entry account_enroll_guard base32 base32_contracts.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition metadata_result a dst :=
 slice_write (slice_write (slice_write dst 0
 [account_digits a;account_period a;Z.of_nat (length (account_label a));Z.of_nat (length (account_issuer a))])
 4 (account_label a)) 132 (account_issuer a).
Lemma encoding_entry_lookup next slots i entry j :
 Forall valid_slot slots -> slots !! i = Some entry -> (j<390)%nat ->
 session_encoding next slots !! (2+390*i+j)%nat = slot_words entry !! j.
Proof.
 intros Hvalid Hlookup Hj. rewrite (encoding_slot_decompose next slots i entry Hlookup).
 set (prefix := [next;Z.of_nat (length (slot_accounts slots))] ++ flat_map slot_words (take i slots)).
 assert (Hprefix : length prefix = (2+390*i)%nat).
 { unfold prefix. rewrite length_app encoded_slots_length; [rewrite length_take; simpl; pose proof (lookup_lt_Some _ _ _ Hlookup); lia|].
   apply Forall_take. exact Hvalid. }
 replace (2+390*i+j)%nat with (length prefix+j)%nat by lia.
 rewrite lookup_app_r; [|lia].
 replace (length prefix+j-length prefix)%nat with j by lia.
 rewrite lookup_app_l; [reflexivity|].
 rewrite slot_words_length; [exact Hj|apply (proj1 (Forall_lookup _ _) Hvalid i entry Hlookup)].
Qed.
Lemma encoding_entry_take next slots i entry j count :
 Forall valid_slot slots -> slots !! i = Some entry -> (j+count<=390)%nat ->
 take count (drop (2+390*i+j) (session_encoding next slots)) = take count (drop j (slot_words entry)).
Proof.
 intros Hvalid Hlookup Hbounds. rewrite (encoding_slot_decompose next slots i entry Hlookup).
 set (prefix := [next;Z.of_nat (length (slot_accounts slots))] ++ flat_map slot_words (take i slots)).
 assert (Hprefix : length prefix = (2+390*i)%nat).
 { unfold prefix. rewrite length_app encoded_slots_length; [rewrite length_take; simpl; pose proof (lookup_lt_Some _ _ _ Hlookup); lia|].
   apply Forall_take. exact Hvalid. }
 assert (Hentry : length (slot_words entry) = 390%nat).
 { apply slot_words_length. apply (proj1 (Forall_lookup _ _) Hvalid i entry Hlookup). }
 replace (2+390*i+j)%nat with (length prefix+j)%nat by lia.
 rewrite drop_app_add drop_app_le; [|lia]. rewrite take_app_le; [reflexivity|].
 rewrite length_drop Hentry. lia.
Qed.
Lemma slot_label_view a :
 take (length (account_label a)) (drop 6 (slot_words (Some a))) = account_label a.
Proof.
 change (take (length (account_label a))
   (padded_field (account_label a) ++ padded_field (account_issuer a) ++ padded_field (account_secret a)) = account_label a).
 unfold padded_field at 1. rewrite <- app_assoc. apply take_app_length.
Qed.
Lemma slot_issuer_view a : account_valid a ->
 take (length (account_issuer a)) (drop 134 (slot_words (Some a))) = account_issuer a.
Proof.
 intros [_ [Hl Hrest]].
 change (take (length (account_issuer a))
   (drop 128 (padded_field (account_label a) ++ padded_field (account_issuer a) ++ padded_field (account_secret a))) = account_issuer a).
 replace 128%nat with (length (padded_field (account_label a))) at 1 by (rewrite padded_field_length; lia).
 rewrite drop_app_length. unfold padded_field at 1. rewrite <- app_assoc. apply take_app_length.
Qed.
Lemma slot_secret_view a : account_valid a ->
 take (length (account_secret a)) (drop 262 (slot_words (Some a))) = account_secret a.
Proof.
 intros [_ [Hl [Hi Hrest]]].
 change (take (length (account_secret a))
   (drop 256 (padded_field (account_label a) ++ padded_field (account_issuer a) ++ padded_field (account_secret a))) = account_secret a).
 replace 256%nat with (length (padded_field (account_label a))+128)%nat at 1 by (rewrite padded_field_length; lia).
 rewrite drop_app_add.
 replace 128%nat with (length (padded_field (account_issuer a))) at 1 by (rewrite padded_field_length; lia).
 rewrite drop_app_length. unfold padded_field. apply take_app_length.
Qed.
Lemma account_ids_injective xs a b : List.NoDup (map account_id xs) ->
 In a xs -> In b xs -> account_id a = account_id b -> a=b.
Proof.
 induction xs as [|c xs IH]; simpl; [tauto|].
 intros Hunique Ha Hb Heq. inversion Hunique as [|? ? Hnotin Htail]; subst.
 destruct Ha as [<-|Ha]; destruct Hb as [<-|Hb]; [reflexivity| | |eapply IH; eauto].
 - exfalso. apply Hnotin. apply in_map_iff. exists b. auto.
 - exfalso. apply Hnotin. apply in_map_iff. exists a. auto.
Qed.
Lemma selected_find_account s slots i a :
 session_valid s -> Permutation (slot_accounts slots) (accounts s) ->
 slots !! i = Some (Some a) -> find_account s (account_id a) = Some a.
Proof.
 intros [_ [_ [Hunique Hrest]]] Hperm Hlookup.
 assert (Hin : In a (accounts s)).
 { eapply Permutation_in; [exact Hperm|]. eapply slot_account_member; eauto. }
 destruct (find_account_present s a Hin) as [found Hfound].
 pose proof Hfound as Hsome. unfold find_account in Hsome.
 apply List.find_some in Hsome as [Hmember Hid]. apply Z.eqb_eq in Hid.
 assert (Heq : found=a) by (eapply account_ids_injective; eauto).
 subst found. exact Hfound.
Qed.
Lemma represented_metadata_lengths words s : represents_session words s -> metadata_lengths_valid words.
Proof.
 intros [slots [Hlen [Hvalid [Hperm ->]]]] i Hi. unfold slot_offset.
 destruct (lookup_lt_is_Some_2 slots i ltac:(lia)) as [entry Hlookup].
 rewrite (encoding_entry_lookup _ _ _ _ 3 Hvalid Hlookup ltac:(lia))
   (encoding_entry_lookup _ _ _ _ 4 Hvalid Hlookup ltac:(lia)).
 pose proof (proj1 (Forall_lookup _ _) Hvalid i entry Hlookup) as Ha.
 destruct entry as [a|].
 - change (0 <= Z.of_nat (length (account_label a)) <= 128 /\ 0 <= Z.of_nat (length (account_issuer a)) <= 128).
   destruct Ha as [_ [Hl [Hissuer Hrest]]]. lia.
 - change (0<=0<=128 /\ 0<=0<=128). lia.
Qed.
Lemma represented_code_slots words s : represents_session words s -> code_slots_valid words.
Proof.
 intros [slots [Hlen [Hvalid [Hperm ->]]]] i Hi Hpositive.
 destruct (lookup_lt_is_Some_2 slots i ltac:(lia)) as [entry Hlookup].
 rewrite (encoded_identifier_lookup _ _ _ _ Hvalid Hlookup) in Hpositive.
 destruct entry as [a|]; [|simpl in Hpositive; lia].
 pose proof (proj1 (Forall_lookup _ _) Hvalid i (Some a) Hlookup) as Ha.
 pose proof Ha as Hfields. destruct Hfields as [_ [Hl [Hissuer [Hs [Hlb [Hib [Hsb Hp]]]]]]].
 unfold entry_offset,entry_secret.
 rewrite (encoding_entry_lookup _ _ _ _ 5 Hvalid Hlookup ltac:(lia))
   (encoding_entry_lookup _ _ _ _ 1 Hvalid Hlookup ltac:(lia))
   (encoding_entry_lookup _ _ _ _ 2 Hvalid Hlookup ltac:(lia)).
 change (1 <= Z.of_nat (length (account_secret a)) <= 128 /\
   Forall byte (take (Z.to_nat (Z.of_nat (length (account_secret a))))
     (drop (2+390*i+262) (session_encoding (next_id s) slots))) /\
   valid_parameters (account_digits a) (account_period a)).
 rewrite Nat2Z.id (encoding_entry_take _ _ _ _ 262 (length (account_secret a)) Hvalid Hlookup ltac:(lia))
   (slot_secret_view a Ha). split; [lia|]. split; assumption.
Qed.
Lemma metadata_encoding_entry next slots i a dst :
 Forall valid_slot slots -> slots !! i = Some (Some a) ->
 metadata_words (session_encoding next slots) i dst = metadata_result a dst.
Proof.
 intros Hvalid Hlookup.
 pose proof (proj1 (Forall_lookup _ _) Hvalid i (Some a) Hlookup) as Ha.
 pose proof Ha as Hfields. destruct Hfields as [_ [Hl [Hissuer Hrest]]].
 unfold metadata_words,slot_offset.
 rewrite (encoding_entry_lookup _ _ _ _ 3 Hvalid Hlookup ltac:(lia))
   (encoding_entry_lookup _ _ _ _ 4 Hvalid Hlookup ltac:(lia)).
 change (slice_write (slice_write (slice_write dst 0 (take 4 (drop (2+390*i+1) (session_encoding next slots))))
   4 (take (Z.to_nat (Z.of_nat (length (account_label a)))) (drop (2+390*i+6) (session_encoding next slots))))
   132 (take (Z.to_nat (Z.of_nat (length (account_issuer a)))) (drop (2+390*i+134) (session_encoding next slots))) = metadata_result a dst).
 rewrite !Nat2Z.id.
 rewrite (encoding_entry_take _ _ _ _ 1 4 Hvalid Hlookup ltac:(lia))
   (encoding_entry_take _ _ _ _ 6 (length (account_label a)) Hvalid Hlookup ltac:(lia))
   (encoding_entry_take _ _ _ _ 134 (length (account_issuer a)) Hvalid Hlookup ltac:(lia))
   slot_label_view (slot_issuer_view a Ha).
 unfold metadata_result. reflexivity.
Qed.
Lemma encoded_find_absent s slots id :
 Forall valid_slot slots -> Permutation (slot_accounts slots) (accounts s) ->
 scan_identifiers (session_encoding (next_id s) slots) id (length slots) = -1 -> find_account s id = None.
Proof.
 intros Hvalid Hperm Habs. apply find_account_absent. intros a Hin.
 apply (scan_encoded_absent (next_id s) slots id Hvalid Habs).
 eapply Permutation_in; [symmetry; exact Hperm|exact Hin].
Qed.
Lemma represented_found_test words s id : session_valid s -> represents_session words s ->
 bool_decide (0 <= scan_identifiers words id 16) = bool_decide (find_account s id <> None).
Proof.
 intros Hsession [slots [Hlen [Hvalid [Hperm ->]]]].
 destruct (scan_identifiers_range (session_encoding (next_id s) slots) id 16) as [Habs|Hfound].
 - assert (Hnone : find_account s id=None) by (apply (encoded_find_absent s slots id Hvalid Hperm); rewrite Hlen; exact Habs).
   rewrite Habs Hnone !bool_decide_false; auto; lia.
 - assert (Hfound' : 0<=scan_identifiers (session_encoding (next_id s) slots) id (length slots)) by (rewrite Hlen; lia).
   destruct (scan_encoded_present _ _ _ Hvalid Hfound') as [i [a [Hlookup [Hscan Hid]]]].
   pose proof (selected_find_account s slots i a Hsession Hperm Hlookup) as Hfind. rewrite Hid in Hfind.
   rewrite Hfind !bool_decide_true; [reflexivity|discriminate|lia].
Qed.
Lemma represented_read_result words s id dst : session_valid s -> represents_session words s ->
 read_words words id dst = match find_account s id with Some a => metadata_result a dst | None => dst end.
Proof.
 intros Hsession [slots [Hlen [Hvalid [Hperm ->]]]].
 destruct (scan_identifiers_range (session_encoding (next_id s) slots) id 16) as [Habs|Hfound].
 - pose proof (encoded_find_absent s slots id Hvalid Hperm ltac:(rewrite Hlen; exact Habs)) as Hfind.
   unfold read_words. rewrite Habs Hfind. reflexivity.
 - assert (Hfound' : 0<=scan_identifiers (session_encoding (next_id s) slots) id (length slots)) by (rewrite Hlen; lia).
   destruct (scan_encoded_present _ _ _ Hvalid Hfound') as [i [a [Hlookup [Hscan Hid]]]].
   pose proof (selected_find_account s slots i a Hsession Hperm Hlookup) as Hfind. rewrite Hid in Hfind.
   assert (Hscan16 : scan_identifiers (session_encoding (next_id s) slots) id 16=Z.of_nat i) by (rewrite <- Hlen; exact Hscan).
   unfold read_words. rewrite Hscan16 Hfind bool_decide_true; [|lia].
   rewrite Nat2Z.id. apply metadata_encoding_entry; assumption.
Qed.
Lemma represented_code_value words s id timestamp : session_valid s -> represents_session words s ->
 session_code_value words id timestamp =
 match find_account s id with Some a => totp (account_secret a) timestamp (account_period a) (account_digits a) | None => -1 end.
Proof.
 intros Hsession [slots [Hlen [Hvalid [Hperm ->]]]].
 destruct (scan_identifiers_range (session_encoding (next_id s) slots) id 16) as [Habs|Hfound].
 - pose proof (encoded_find_absent s slots id Hvalid Hperm ltac:(rewrite Hlen; exact Habs)) as Hfind.
   unfold session_code_value. rewrite Habs Hfind. reflexivity.
 - assert (Hfound' : 0<=scan_identifiers (session_encoding (next_id s) slots) id (length slots)) by (rewrite Hlen; lia).
   destruct (scan_encoded_present _ _ _ Hvalid Hfound') as [i [a [Hlookup [Hscan Hid]]]].
   pose proof (selected_find_account s slots i a Hsession Hperm Hlookup) as Hfind. rewrite Hid in Hfind.
   assert (Hscan16 : scan_identifiers (session_encoding (next_id s) slots) id 16=Z.of_nat i) by (rewrite <- Hlen; exact Hscan).
   pose proof (proj1 (Forall_lookup _ _) Hvalid i (Some a) Hlookup) as Ha.
   pose proof Ha as Hfields. destruct Hfields as [_ [Hl [Hi [Hs Hrest]]]].
   unfold session_code_value. rewrite Hscan16 Hfind bool_decide_true; [|lia]. rewrite Nat2Z.id.
   unfold entry_secret,entry_offset.
   rewrite (encoding_entry_lookup _ _ _ _ 5 Hvalid Hlookup ltac:(lia))
     (encoding_entry_lookup _ _ _ _ 2 Hvalid Hlookup ltac:(lia))
     (encoding_entry_lookup _ _ _ _ 1 Hvalid Hlookup ltac:(lia)).
   change (totp (take (Z.to_nat (Z.of_nat (length (account_secret a))))
     (drop (2+390*i+262) (session_encoding (next_id s) slots))) timestamp (account_period a) (account_digits a) =
     totp (account_secret a) timestamp (account_period a) (account_digits a)).
   rewrite Nat2Z.id (encoding_entry_take _ _ _ _ 262 (length (account_secret a)) Hvalid Hlookup ltac:(lia))
     (slot_secret_view a Ha). reflexivity.
Qed.
Lemma metadata_runtime_check label issuer : metadata_validb label issuer =
 if bool_decide ((1<=length label<=128)%nat /\ (length issuer<=128)%nat)
 then (bytes_test label && bytes_test issuer)%bool else false.
Proof.
 apply Bool.eq_true_iff_eq. rewrite metadata_validb_spec.
 destruct (decide ((1<=length label<=128)%nat /\ (length issuer<=128)%nat)) as [Hbounds|Hbounds].
 - rewrite bool_decide_true; [|exact Hbounds]. rewrite Bool.andb_true_iff !bytes_test_spec.
   unfold metadata_valid. tauto.
 - rewrite bool_decide_false; [|exact Hbounds]. unfold metadata_valid. split; [tauto|discriminate].
Qed.
Lemma metadata_runtime_result label issuer found :
 (if bool_decide ((1<=length label<=128)%nat /\ (length issuer<=128)%nat)
 then (bytes_test label && bytes_test issuer) && found else false)%bool =
 (metadata_validb label issuer && found)%bool.
Proof. rewrite metadata_runtime_check. destruct (bool_decide _), (bytes_test label && bytes_test issuer)%bool; reflexivity. Qed.
Lemma metadata_runtime_words label issuer (words renamed : list Z) :
 (if bool_decide ((1<=length label<=128)%nat /\ (length issuer<=128)%nat)
 then (if bytes_test label && bytes_test issuer then renamed else words) else words) =
 if metadata_validb label issuer then renamed else words.
Proof. rewrite metadata_runtime_check. destruct (bool_decide _), (bytes_test label && bytes_test issuer)%bool; reflexivity. Qed.
Lemma rename_result_valid s id label issuer : session_valid s ->
 session_valid (snd (rename_account s id label issuer)).
Proof.
 intros Hs. destruct (rename_account s id label issuer) as [success s'] eqn:Hr.
 simpl. eapply rename_preserves_validity; eauto.
Qed.
Lemma abstract_code_result words s id timestamp : session_valid s -> represents_session words s ->
 (if bool_decide (0<=timestamp) then session_code_value words id timestamp else -1) =
 match code_for s id timestamp with Some code => code | None => -1 end.
Proof.
 intros Hs Hw. rewrite (represented_code_value _ _ _ _ Hs Hw). unfold code_for.
 destruct (decide (0<=timestamp)) as [Htime|Htime].
 - rewrite bool_decide_true; [|exact Htime]. rewrite (proj2 (Z.leb_le _ _) Htime).
   destruct (find_account s id); reflexivity.
 - rewrite bool_decide_false; [|exact Htime]. rewrite (proj2 (Z.leb_gt 0 timestamp) ltac:(lia)).
   destruct (find_account s id); reflexivity.
Qed.
Section ports.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Definition session_at p s : iProp Σ :=
 ∃ words, ⌜represents_session words s⌝ ∗ array.array_cells p words.
Theorem core_new_wp :
 ⊢ WP new_body {{u, ∃ p, ⌜u=LitV (LitPtr p) /\ session_valid empty_session⌝ ∗
   RawId p ↦ᵦ 6242%nat ∗ session_at p empty_session}}.
Proof.
 iApply (wp_wand with "[]"); [iApply session_new_wp|].
 iIntros (u) "H". iDestruct "H" as (p) "[%Hu [Hblock Hcells]]".
 iExists p. iSplit; [iPureIntro; split; [exact Hu|apply empty_session_valid]|].
 iFrame "Hblock". iExists (1::replicate 6241 0%Z). iFrame.
 iPureIntro. apply initialized_session_representation.
Qed.
Theorem core_destroy_wp p s : session_at p s -∗ RawId p ↦ᵦ 6242%nat -∗
 WP call destroy_body [pv p] {{u, ⌜u=LitV LitUnit⌝}}.
Proof.
 iIntros "Hsession Hblock". iDestruct "Hsession" as (words) "[%Hrep Hcells]".
 iApply (session_destroy_wp with "Hcells Hblock"). eapply represented_session_length; eauto.
Qed.
Theorem core_list_wp p s q dst : (16<=length dst)%nat -> session_valid s ->
 session_at p s -∗ array.array_cells q dst -∗
 WP call list_body [pv p;pv q]
 {{u, ∃ ids, ⌜u=LitV (LitInt (Z.of_nat (length ids))) /\ Permutation ids (map account_id (accounts s))⌝ ∗
   session_at p s ∗ array.array_cells q (ids++drop (length ids) dst)}}.
Proof.
 intros Hdst Hvalid. iIntros "Hsession Hdst". iDestruct "Hsession" as (words) "[%Hrep Hcells]".
 iApply (wp_wand with "[Hcells Hdst]").
 { iApply (session_list_wp with "Hcells Hdst"); [eapply represented_session_length; eauto|exact Hdst]. }
 iIntros (u) "[%Hu [Hcells Hdst]]". iExists (live_identifiers words 16). iFrame "Hdst".
 iSplit; [iPureIntro; split; [exact Hu|eapply represented_session_listing; eauto]|].
 iExists words. iFrame. done.
Qed.
Theorem core_read_wp p s id q dst : (260<=length dst)%nat -> session_valid s ->
 session_at p s -∗ array.array_cells q dst -∗
 WP call read_body [pv p;int id;pv q]
 {{u, ⌜u=LitV (LitBool (bool_decide (find_account s id <> None)))⌝ ∗ session_at p s ∗
   array.array_cells q (match find_account s id with Some a => metadata_result a dst | None => dst end)}}.
Proof.
 intros Hdst Hvalid. iIntros "Hsession Hdst". iDestruct "Hsession" as (words) "[%Hrep Hcells]".
 iApply (wp_wand with "[Hcells Hdst]").
 { iApply (session_read_wp with "Hcells Hdst"); [eapply represented_session_length; eauto|exact Hdst|].
   eapply represented_metadata_lengths; eauto. }
 iIntros (u) "[%Hu [Hcells Hdst]]".
 rewrite (represented_found_test words s id Hvalid Hrep) in Hu.
 iEval (rewrite (represented_read_result words s id dst Hvalid Hrep)) in "Hdst".
 iFrame "Hdst". iSplit; [done|]. iExists words. iFrame. done.
Qed.
Theorem core_remove_wp p s id : session_valid s -> session_at p s -∗
 WP call remove_body [pv p;int id]
 {{u, ⌜u=LitV (LitBool (bool_decide (find_account s id <> None))) /\ session_valid (remove_account s id)⌝ ∗
   session_at p (remove_account s id)}}.
Proof.
 intros Hvalid. iIntros "Hsession". iDestruct "Hsession" as (words) "[%Hrep Hcells]".
 iApply (wp_wand with "[Hcells]").
 { iApply (session_remove_wp with "Hcells"). eapply represented_session_length; eauto. }
 iIntros (u) "[%Hu Hcells]". rewrite (represented_found_test words s id Hvalid Hrep) in Hu.
 iSplit; [iPureIntro; split; [exact Hu|apply remove_preserves_validity; exact Hvalid]|].
 iExists (removed_words words id). iFrame. iPureIntro. apply removed_words_represents; assumption.
Qed.
Theorem core_rename_wp heap p s id lp label ip issuer :
 session_valid s -> buffer_in heap lp label -> buffer_in heap ip issuer ->
 input_cells heap -∗ session_at p s -∗
 WP call rename_body [pv p;int id;pv lp;int (Z.of_nat (length label));pv ip;int (Z.of_nat (length issuer))]
 {{u, ⌜u=LitV (LitBool (fst (rename_account s id label issuer))) /\ session_valid (snd (rename_account s id label issuer))⌝ ∗
   input_cells heap ∗ session_at p (snd (rename_account s id label issuer))}}.
Proof.
 intros Hvalid Hl Hi. iIntros "Hheap Hsession". iDestruct "Hsession" as (words) "[%Hrep Hcells]".
 iApply (wp_wand with "[Hcells Hheap]").
 { iApply (session_rename_all_lengths_wp with "Hheap Hcells"); [eapply represented_session_length; eauto|exact Hl|exact Hi]. }
 iIntros (u) "[%Hu [Hheap Hcells]]".
 rewrite metadata_runtime_result in Hu. iEval (rewrite metadata_runtime_words) in "Hcells".
 iFrame "Hheap". destruct (metadata_validb label issuer) eqn:Hmeta.
 - apply metadata_validb_spec in Hmeta.
   destruct (renamed_words_refines words s id label issuer Hvalid Hrep Hmeta) as [Hreturn Hupdated].
   cbn [andb] in Hu. rewrite <- Hreturn in Hu.
   iSplit; [iPureIntro; split; [exact Hu|apply rename_result_valid; exact Hvalid]|].
   iExists (renamed_words words id label issuer). iFrame. done.
 - unfold rename_account. rewrite Hmeta. simpl. iSplit; [iPureIntro; split; [exact Hu|exact Hvalid]|].
   iExists words. iFrame. done.
Qed.
Theorem core_code_wp p s id timestamp : session_valid s -> session_at p s -∗
 WP call code_body [pv p;int id;int timestamp]
 {{u, ⌜u=LitV (LitInt (match code_for s id timestamp with Some code => code | None => -1 end))⌝ ∗ session_at p s}}.
Proof.
 intros Hvalid. iIntros "Hsession". iDestruct "Hsession" as (words) "[%Hrep Hcells]".
 iApply (wp_wand with "[Hcells]").
 { iApply (session_code_wp with "Hcells"); [eapply represented_session_length; eauto|]. eapply represented_code_slots; eauto. }
 iIntros (u) "[%Hu Hcells]". rewrite (abstract_code_result words s id timestamp Hvalid Hrep) in Hu.
 iSplit; [done|]. iExists words. iFrame. done.
Qed.
End ports.
Definition enroll_encoded s label issuer chars digits period :=
 match base32.decode chars with
 | None => (-1,s)
 | Some secret => enroll s label issuer secret digits period
 end.
Lemma decode_input_length chars secret : base32.decode chars = Some secret ->
 (2<=length chars<=208)%nat.
Proof.
 unfold base32.decode. destruct ((2<=?length chars)&&(length chars<=?208))%nat eqn:Hsize; [|discriminate].
 intros _. apply Bool.andb_true_iff in Hsize as [Hlo Hhi]. apply Nat.leb_le in Hlo,Hhi. lia.
Qed.
Lemma valid_input_iff label issuer secret digits period :
 valid_input label issuer secret digits period = true <->
 metadata_valid label issuer /\ (1<=length secret<=128)%nat /\ Forall byte secret /\ valid_parameters digits period.
Proof.
 unfold valid_input,metadata_valid,valid_parameters. repeat rewrite Bool.andb_true_iff.
 rewrite !Nat.leb_le !byte_check_spec Bool.orb_true_iff !Z.eqb_eq !Z.leb_le. tauto.
Qed.
Lemma decoded_input_check label issuer chars secret digits period : base32.decode chars = Some secret ->
 valid_input label issuer secret digits period =
 (bool_decide (enrollment_numbers label issuer chars digits period) && bytes_test label && bytes_test issuer)%bool.
Proof.
 intros Hdecode. pose proof (decode_input_length _ _ Hdecode) as Hchars.
 pose proof (base32_contracts.decode_length _ _ Hdecode) as Hsecret.
 pose proof (base32.decode_bytes _ _ Hdecode) as Hbytes.
 apply Bool.eq_true_iff_eq. rewrite valid_input_iff !Bool.andb_true_iff !bytes_test_spec bool_decide_eq_true.
 unfold enrollment_numbers,metadata_valid. tauto.
Qed.
Lemma represented_available_slot words s : represents_session words s -> available_slot words.
Proof.
 intros [slots [Hlen [Hvalid [Hperm ->]]]]. unfold available_slot.
 change (Z.of_nat (length (slot_accounts slots))<=15 -> exists i, (i<16)%nat /\ slot_identifier (session_encoding (next_id s) slots) i=0).
 intros Hroom. destruct (vacant_slot_exists slots ltac:(lia)) as [i Hlookup].
 exists i. split; [pose proof (lookup_lt_Some _ _ _ Hlookup); lia|].
 rewrite (encoded_identifier_lookup _ _ _ _ Hvalid Hlookup). reflexivity.
Qed.
Lemma decoded_enrollment_result words s label issuer secret digits period :
 represents_session words s -> valid_input label issuer secret digits period = true ->
 (1<=length secret)%nat ->
 enroll_decoded_result words (Z.of_nat (length secret)) = fst (enroll s label issuer secret digits period).
Proof.
 intros [slots [Hlen [Hvalid [Hperm ->]]]] Hinput Hsecret.
 unfold enroll_decoded_result,enroll. rewrite Hinput.
 change ((if bool_decide (1<=Z.of_nat (length secret)) then
   if bool_decide (Z.of_nat (length (slot_accounts slots))<=15) then
   if bool_decide (next_id s<=9223372036854775806) then next_id s else -3 else -2 else -1) =
   fst (if (length (accounts s) <?16)%nat then
   if (next_id s<=?9223372036854775806)%Z then
    (next_id s,Session (next_id s+1) (accounts s++[Account (next_id s) label issuer secret digits period]))
   else (-3,s) else (-2,s))).
 rewrite (Permutation_length Hperm) bool_decide_true; [|lia].
 destruct (decide ((length (accounts s)<16)%nat)) as [Hroom|Hroom].
 - rewrite bool_decide_true; [|lia]. rewrite (proj2 (Nat.ltb_lt _ _) Hroom).
   destruct (decide (next_id s<=9223372036854775806)) as [Hnext|Hnext].
   + rewrite bool_decide_true; [|exact Hnext]. rewrite (proj2 (Z.leb_le _ _) Hnext). reflexivity.
   + rewrite bool_decide_false; [|exact Hnext]. rewrite (proj2 (Z.leb_gt (next_id s) 9223372036854775806) ltac:(lia)). reflexivity.
 - rewrite bool_decide_false; [|lia]. rewrite (proj2 (Nat.ltb_ge (length (accounts s)) 16) ltac:(lia)). reflexivity.
Qed.
Lemma decoded_enrollment_represents words s label issuer secret digits period :
 session_valid s -> represents_session words s -> valid_input label issuer secret digits period = true ->
 (1<=length secret)%nat ->
 represents_session (enroll_decoded_words words label issuer secret (Z.of_nat (length secret)) digits period)
   (snd (enroll s label issuer secret digits period)).
Proof.
 intros Hvalid Hrep Hinput Hsecret. unfold enroll_decoded_words.
 rewrite bool_decide_true; [|lia]. rewrite Nat2Z.id take_ge; [|lia].
 assert (Hcount : default 0 (words !! 1%nat) = Z.of_nat (length (accounts s))).
 { destruct Hrep as [slots [Hlen [Hslots [Hperm ->]]]]. change (Z.of_nat (length (slot_accounts slots)) = Z.of_nat (length (accounts s))).
   rewrite (Permutation_length Hperm). reflexivity. }
 assert (Hnextid : default 0 (words !! 0%nat) = next_id s).
 { destruct Hrep as [slots [Hlen [Hslots [Hperm ->]]]]. reflexivity. }
 rewrite Hcount Hnextid.
 destruct (decide ((length (accounts s)<16)%nat)) as [Hroom|Hroom].
 - rewrite bool_decide_true; [|lia].
   destruct (decide (next_id s<=9223372036854775806)) as [Hnext|Hnext].
   + rewrite bool_decide_true; [|exact Hnext]. apply enrolled_words_represents; assumption.
   + rewrite bool_decide_false; [|exact Hnext].
     unfold enroll. rewrite Hinput (proj2 (Nat.ltb_lt _ _) Hroom) (proj2 (Z.leb_gt (next_id s) 9223372036854775806) ltac:(lia)). exact Hrep.
 - rewrite bool_decide_false; [|lia].
   unfold enroll. rewrite Hinput (proj2 (Nat.ltb_ge (length (accounts s)) 16) ltac:(lia)). exact Hrep.
Qed.
Lemma enrollment_refines words s label issuer chars digits period :
 session_valid s -> represents_session words s ->
 enrollment_result words label issuer chars digits period = fst (enroll_encoded s label issuer chars digits period) /\
 represents_session (enrollment_words words label issuer chars digits period)
   (snd (enroll_encoded s label issuer chars digits period)).
Proof.
 intros Hvalid Hrep. unfold enrollment_result,enrollment_words,enroll_encoded.
 destruct (base32.decode chars) as [secret|] eqn:Hdecode.
 - pose proof (decoded_input_check label issuer chars secret digits period Hdecode) as Hcheck.
   pose proof (base32_contracts.decode_length _ _ Hdecode) as Hsecret.
   destruct (bool_decide (enrollment_numbers label issuer chars digits period)) eqn:Hnumbers;
   destruct (bytes_test label && bytes_test issuer)%bool eqn:Hbytes.
   + assert (Hinput : valid_input label issuer secret digits period=true).
     { rewrite Hcheck. cbn [andb]. exact Hbytes. }
     split; [apply decoded_enrollment_result; auto; lia|apply decoded_enrollment_represents; auto; lia].
   + assert (Hinput : valid_input label issuer secret digits period=false).
     { rewrite Hcheck. cbn [andb]. exact Hbytes. }
     unfold enroll. rewrite Hinput. split; [reflexivity|exact Hrep].
   + assert (Hinput : valid_input label issuer secret digits period=false) by (rewrite Hcheck; reflexivity).
     unfold enroll. rewrite Hinput. split; [reflexivity|exact Hrep].
   + assert (Hinput : valid_input label issuer secret digits period=false) by (rewrite Hcheck; reflexivity).
     unfold enroll. rewrite Hinput. split; [reflexivity|exact Hrep].
 - destruct (bool_decide (enrollment_numbers label issuer chars digits period));
   destruct (bytes_test label && bytes_test issuer)%bool; split; [reflexivity|exact Hrep|reflexivity|exact Hrep|reflexivity|exact Hrep|reflexivity|exact Hrep].
Qed.
Lemma enroll_encoded_valid s label issuer chars digits period : session_valid s ->
 session_valid (snd (enroll_encoded s label issuer chars digits period)).
Proof.
 intros Hvalid. unfold enroll_encoded. destruct (base32.decode chars) as [secret|]; [|exact Hvalid].
 destruct (enroll s label issuer secret digits period) as [code s'] eqn:Henroll.
 simpl. eapply enroll_preserves_validity; eauto.
Qed.
Section enrollment_port.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem core_enroll_wp heap p s lp label ip issuer sp chars digits period :
 session_valid s -> buffer_in heap lp label -> buffer_in heap ip issuer -> buffer_in heap sp chars ->
 input_cells heap -∗ session_at p s -∗
 WP call add_body [pv p;pv lp;int (Z.of_nat (length label));pv ip;int (Z.of_nat (length issuer));
   pv sp;int (Z.of_nat (length chars));int digits;int period]
 {{u, ⌜u=LitV (LitInt (fst (enroll_encoded s label issuer chars digits period))) /\
   session_valid (snd (enroll_encoded s label issuer chars digits period))⌝ ∗
   input_cells heap ∗ session_at p (snd (enroll_encoded s label issuer chars digits period))}}.
Proof.
 intros Hvalid Hl Hi Hsecret. iIntros "Hheap Hsession".
 iDestruct "Hsession" as (words) "[%Hrep Hcells]".
 iApply (wp_wand with "[Hheap Hcells]").
 { iApply (session_enroll_wp with "Hheap Hcells");
   [eapply represented_session_length; eauto|eapply represented_available_slot; eauto|exact Hl|exact Hi|exact Hsecret]. }
 iIntros (u) "[%Hu [Hheap Hcells]]".
 destruct (enrollment_refines words s label issuer chars digits period Hvalid Hrep) as [Hreturn Hupdated].
 rewrite Hreturn in Hu. iFrame "Hheap".
 iSplit; [iPureIntro; split; [exact Hu|apply enroll_encoded_valid; exact Hvalid]|].
 iExists (enrollment_words words label issuer chars digits period). iFrame. done.
Qed.
End enrollment_port.
