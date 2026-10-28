(** Abstract account membership and physical slot order are related by
    permutation. Updates retain canonical zero padding and exact occupancy. *)
From Coq Require Import ZArith List Lia Bool Sorting.Permutation.
From iris.proofmode Require Import proofmode.
From cjr.authenticator Require Import accounts account_model sessions account_refinement.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.
Lemma lookup_nth_error {A} (xs : list A) i : xs !! i = nth_error xs i.
Proof. revert xs. induction i; intros [|x xs]; simpl; auto. Qed.
Lemma encoded_identifier_lookup next slots i entry :
 Forall valid_slot slots -> slots !! i = Some entry ->
 slot_identifier (session_encoding next slots) i = entry_id entry.
Proof.
 intros Hvalid Hentry. unfold slot_identifier. rewrite lookup_nth_error.
 rewrite (session_encoding_identifier next slots i entry Hvalid); [reflexivity|].
 rewrite <- lookup_nth_error. exact Hentry.
Qed.
Lemma slots_prefix_listing next slots count :
 Forall valid_slot slots -> (count <= length slots)%nat ->
 live_identifiers (session_encoding next slots) count =
 map account_id (slot_accounts (take count slots)).
Proof.
 intros Hvalid. induction count as [|count IH]; intros Hcount.
 - rewrite live_identifiers_zero. reflexivity.
 - rewrite live_identifiers_succ IH; [|lia].
   destruct (lookup_lt_is_Some_2 slots count ltac:(lia)) as [entry Hentry].
   rewrite (encoded_identifier_lookup _ _ _ _ Hvalid Hentry) (take_S_r _ _ _ Hentry).
   rewrite slot_accounts_app map_app. destruct entry as [a|]; simpl.
   + assert (Ha : account_valid a).
     { apply (proj1 (Forall_lookup _ _) Hvalid count (Some a) Hentry). }
     unfold account_valid in Ha. rewrite bool_decide_true; [reflexivity|lia].
   + rewrite app_nil_r; reflexivity.
Qed.
Theorem session_listing_slot_order next slots : Forall valid_slot slots ->
 live_identifiers (session_encoding next slots) (length slots) = map account_id (slot_accounts slots).
Proof.
 intros Hvalid. rewrite slots_prefix_listing; [rewrite take_ge; auto|exact Hvalid|lia].
Qed.
Theorem represented_session_listing words s : represents_session words s ->
 Permutation (live_identifiers words 16) (map account_id (accounts s)).
Proof.
 intros [slots [Hlen [Hvalid [Hperm ->]]]]. rewrite <- Hlen.
 rewrite session_listing_slot_order; [apply Permutation_map; exact Hperm|exact Hvalid].
Qed.
Lemma slot_account_member slots i a : slots !! i = Some (Some a) -> In a (slot_accounts slots).
Proof.
 revert slots. induction i; intros [|entry slots] Hentry; simpl in Hentry; try discriminate.
 - inversion Hentry; subst entry. simpl. auto.
 - specialize (IHi _ Hentry). destruct entry; simpl; auto.
Qed.
Lemma boolean_filter_identity {A} (f : A -> bool) xs :
 (forall x, In x xs -> f x = true) -> List.filter f xs = xs.
Proof.
 intros H. induction xs as [|x xs IH]; [reflexivity|].
 simpl. rewrite H; [rewrite IH; [reflexivity|intros y Hy; apply H; right; exact Hy]|left; reflexivity].
Qed.
Lemma slot_accounts_update_none slots i a :
 slots !! i = Some (Some a) -> List.NoDup (map account_id (slot_accounts slots)) ->
 slot_accounts (<[i := None]> slots) =
 List.filter (fun entry => negb (account_id entry =? account_id a)) (slot_accounts slots).
Proof.
 revert slots. induction i as [|i IH]; intros [|entry slots] Hlookup Hunique;
 simpl in Hlookup; try discriminate.
 - inversion Hlookup; subst entry. simpl in Hunique |- *.
   inversion Hunique as [|? ? Hnotin Htail]; subst.
   rewrite Z.eqb_refl. simpl.
   symmetry. apply boolean_filter_identity. intros b Hb.
   apply Bool.negb_true_iff. apply Z.eqb_neq. intros Hid.
   apply Hnotin. apply in_map_iff. exists b. split; [exact Hid|exact Hb].
 - destruct entry as [b|]; simpl in Hunique |- *.
   + inversion Hunique as [|? ? Hnotin Htail]; subst.
     assert (Hne : account_id b <> account_id a).
     { intros Heq. apply Hnotin. apply in_map_iff. exists a. split; [symmetry; exact Heq|].
       eapply slot_account_member; eauto. }
     rewrite (proj2 (Z.eqb_neq _ _) Hne). simpl. f_equal. apply IH; assumption.
   + apply IH; assumption.
Qed.
Lemma rename_unmatched xs id label issuer :
 ~ In id (map account_id xs) -> map (rename_one id label issuer) xs = xs.
Proof.
 intros Hnotin. induction xs as [|a xs IH]; [reflexivity|].
 simpl. assert (Hne : account_id a <> id).
 { intros Hid. apply Hnotin. simpl. auto. }
 unfold rename_one at 1. rewrite (proj2 (Z.eqb_neq _ _) Hne).
 f_equal. apply IH. intros Hin. apply Hnotin. simpl. auto.
Qed.
Lemma slot_accounts_update_metadata slots i a label issuer :
 slots !! i = Some (Some a) -> List.NoDup (map account_id (slot_accounts slots)) ->
 slot_accounts (<[i := Some (with_metadata a label issuer)]> slots) =
 map (rename_one (account_id a) label issuer) (slot_accounts slots).
Proof.
 revert slots. induction i as [|i IH]; intros [|entry slots] Hlookup Hunique;
 simpl in Hlookup; try discriminate.
 - inversion Hlookup; subst entry. simpl in Hunique |- *.
   inversion Hunique as [|? ? Hnotin Htail]; subst.
   unfold rename_one at 1. rewrite Z.eqb_refl. f_equal.
   symmetry. apply rename_unmatched. exact Hnotin.
 - destruct entry as [b|]; simpl in Hunique |- *.
   + inversion Hunique as [|? ? Hnotin Htail]; subst.
     assert (Hne : account_id b <> account_id a).
     { intros Heq. apply Hnotin. apply in_map_iff. exists a. split; [symmetry; exact Heq|].
       eapply slot_account_member; eauto. }
     unfold rename_one at 1. rewrite (proj2 (Z.eqb_neq _ _) Hne).
     f_equal. apply IH; assumption.
   + apply IH; assumption.
Qed.
Lemma slot_accounts_fill_empty slots i a : slots !! i = Some None ->
 Permutation (slot_accounts (<[i := Some a]> slots)) (slot_accounts slots ++ [a]).
Proof.
 revert slots. induction i as [|i IH]; intros [|entry slots] Hlookup;
 simpl in Hlookup; try discriminate.
 - inversion Hlookup; subst entry. simpl. pose proof (Permutation_middle (slot_accounts slots) [] a) as Hperm. rewrite app_nil_r in Hperm. exact Hperm.
 - destruct entry as [b|]; simpl; [apply perm_skip|]; apply IH; assumption.
Qed.
Lemma boolean_filter_permutation {A} (f : A -> bool) xs ys :
 Permutation xs ys -> Permutation (List.filter f xs) (List.filter f ys).
Proof.
 intros H. induction H; simpl.
 - constructor.
 - destruct (f x); [constructor|]; exact IHPermutation.
 - destruct (f x), (f y); simpl; try constructor; try reflexivity.
 - eapply Permutation_trans; eauto.
Qed.
Lemma represented_slot_ids_unique s slots :
 session_valid s -> Permutation (slot_accounts slots) (accounts s) ->
 List.NoDup (map account_id (slot_accounts slots)).
Proof.
 intros [_ [_ [Hunique _]]] Hperm.
 eapply Permutation_NoDup; [apply Permutation_map; symmetry; exact Hperm|exact Hunique].
Qed.
Theorem remove_slot_represents s slots i a :
 session_valid s -> length slots = 16%nat -> Forall valid_slot slots ->
 Permutation (slot_accounts slots) (accounts s) -> slots !! i = Some (Some a) ->
 represents_session (session_encoding (next_id s) (<[i := None]> slots))
   (remove_account s (account_id a)).
Proof.
 intros Hsession Hlen Hvalid Hperm Hlookup.
 exists (<[i := None]> slots). rewrite length_insert. split; [exact Hlen|].
 split; [apply Forall_insert; [exact Hvalid|exact I]|]. split; [|reflexivity].
 rewrite (slot_accounts_update_none slots i a); [|exact Hlookup|eapply represented_slot_ids_unique; eauto].
 unfold remove_account; simpl. apply boolean_filter_permutation. exact Hperm.
Qed.
Theorem rename_slot_represents s slots i a label issuer :
 session_valid s -> length slots = 16%nat -> Forall valid_slot slots ->
 Permutation (slot_accounts slots) (accounts s) -> slots !! i = Some (Some a) ->
 metadata_valid label issuer ->
 represents_session
   (session_encoding (next_id s) (<[i := Some (with_metadata a label issuer)]> slots))
   (Session (next_id s) (map (rename_one (account_id a) label issuer) (accounts s))).
Proof.
 intros Hsession Hlen Hvalid Hperm Hlookup Hmetadata.
 exists (<[i := Some (with_metadata a label issuer)]> slots).
 rewrite length_insert. split; [exact Hlen|]. split.
 - apply Forall_insert; [exact Hvalid|]. simpl. apply with_metadata_valid; [|exact Hmetadata].
   apply (proj1 (Forall_lookup _ _) Hvalid i (Some a) Hlookup).
 - split; [|reflexivity].
   rewrite (slot_accounts_update_metadata slots i a label issuer); [apply Permutation_map; exact Hperm|exact Hlookup|].
   eapply represented_slot_ids_unique; eauto.
Qed.
Theorem enroll_slot_represents s slots i a :
 length slots = 16%nat -> Forall valid_slot slots ->
 Permutation (slot_accounts slots) (accounts s) -> slots !! i = Some None -> account_valid a ->
 represents_session (session_encoding (next_id s+1) (<[i := Some a]> slots))
   (Session (next_id s+1) (accounts s ++ [a])).
Proof.
 intros Hlen Hvalid Hperm Hlookup Ha. exists (<[i := Some a]> slots).
 rewrite length_insert. split; [exact Hlen|]. split.
 - apply Forall_insert; [exact Hvalid|exact Ha].
 - split; [|reflexivity]. eapply Permutation_trans.
   + apply slot_accounts_fill_empty. exact Hlookup.
   + apply Permutation_app_tail. exact Hperm.
Qed.
Lemma encoded_slots_replace slots i old entry :
 Forall valid_slot slots -> slots !! i = Some old ->
 flat_map slot_words (<[i := entry]> slots) =
 take (390*i) (flat_map slot_words slots) ++ slot_words entry ++
 drop (390*i+390) (flat_map slot_words slots).
Proof.
 intros Hvalid Hlookup. assert (Hi : (i < length slots)%nat) by (eapply lookup_lt_Some; eauto).
 pose proof (take_drop_middle slots i old Hlookup) as Hsplit.
 assert (Hpre : length (flat_map slot_words (take i slots)) = (390*i)%nat).
 { rewrite encoded_slots_length; [rewrite length_take; lia|apply Forall_take; exact Hvalid]. }
 assert (Hold : length (slot_words old) = 390%nat).
 { apply slot_words_length. apply (proj1 (Forall_lookup _ _) Hvalid i old Hlookup). }
 assert (Htake : take (390*i) (flat_map slot_words slots) = flat_map slot_words (take i slots)).
 { rewrite <- Hsplit at 1. rewrite flat_map_app. simpl flat_map.
   rewrite <- Hpre. apply take_app_length. }
 assert (Hdrop : drop (390*i+390) (flat_map slot_words slots) = flat_map slot_words (drop (S i) slots)).
 { rewrite <- Hsplit at 1. rewrite flat_map_app. simpl flat_map.
   rewrite <- Hpre. rewrite <- Hold. rewrite drop_app.
   rewrite drop_ge; [|lia]. rewrite app_nil_l.
   replace (length (flat_map slot_words (take i slots))+length (slot_words old)-
     length (flat_map slot_words (take i slots)))%nat with (length (slot_words old)) by lia.
   apply drop_app_length. }
 rewrite (insert_take_drop _ _ _ Hi) flat_map_app. simpl flat_map.
 rewrite Htake Hdrop. reflexivity.
Qed.
Lemma slot_account_index slots a : In a (slot_accounts slots) ->
 exists i, slots !! i = Some (Some a).
Proof.
 induction slots as [|entry slots IH]; simpl; [contradiction|].
 destruct entry as [b|]; simpl.
 - intros [<-|Hin]; [exists 0%nat; reflexivity|].
   destruct (IH Hin) as [i Hi]. exists (S i). exact Hi.
 - intros Hin. destruct (IH Hin) as [i Hi]. exists (S i). exact Hi.
Qed.
Lemma scan_encoded_present next slots id : Forall valid_slot slots ->
 0 <= scan_identifiers (session_encoding next slots) id (length slots) ->
 exists i a, slots !! i = Some (Some a) /\
 scan_identifiers (session_encoding next slots) id (length slots) = Z.of_nat i /\ account_id a = id.
Proof.
 intros Hvalid Hfound.
 destruct (scan_identifiers_present _ _ _ Hfound) as [i [Hi [Hscan [Hid Hslot]]]].
 destruct (lookup_lt_is_Some_2 slots i Hi) as [entry Hentry].
 rewrite (encoded_identifier_lookup _ _ _ _ Hvalid Hentry) in Hslot.
 destruct entry as [a|]; [exists i,a; auto|simpl in Hslot; lia].
Qed.
Lemma scan_encoded_absent next slots id : Forall valid_slot slots ->
 scan_identifiers (session_encoding next slots) id (length slots) = -1 ->
 forall a, In a (slot_accounts slots) -> account_id a <> id.
Proof.
 intros Hvalid Habs a Hin Heq. destruct (slot_account_index _ _ Hin) as [i Hi].
 pose proof (proj1 (scan_identifiers_absent _ _ _) Habs) as Hnone.
 destruct (Hnone i ltac:(eapply lookup_lt_Some; eauto)) as [Hsmall|Hne].
 - pose proof (proj1 (Forall_lookup _ _) Hvalid i (Some a) Hi) as Ha.
   unfold valid_slot,account_valid in Ha. lia.
 - rewrite (encoded_identifier_lookup _ _ _ _ Hvalid Hi) in Hne. exact (Hne Heq).
Qed.
Lemma slot_accounts_clear_length slots i a : slots !! i = Some (Some a) ->
 S (length (slot_accounts (<[i := None]> slots))) = length (slot_accounts slots).
Proof.
 revert slots. induction i; intros [|entry slots] Hlookup; simpl in Hlookup; try discriminate.
 - inversion Hlookup; subst entry. reflexivity.
 - destruct entry; simpl; specialize (IHi _ Hlookup); lia.
Qed.
Lemma encoding_clear_slot next slots i old : Forall valid_slot slots -> slots !! i = Some old ->
 account_refinement.cleared_slot (session_encoding next slots) i =
 [next;Z.of_nat (length (slot_accounts slots))] ++ flat_map slot_words (<[i := None]> slots).
Proof.
 intros Hvalid Hlookup. unfold account_refinement.cleared_slot,session_encoding.
 change ([next; Z.of_nat (length (slot_accounts slots))] ++
   (take (390*i) (flat_map slot_words slots) ++ slot_words None ++
    drop (390*i+390) (flat_map slot_words slots)) =
   [next;Z.of_nat (length (slot_accounts slots))] ++ flat_map slot_words (<[i := None]> slots)).
 rewrite <- (encoded_slots_replace slots i old None Hvalid Hlookup). reflexivity.
Qed.
Lemma removed_encoding_present next slots id i a :
 length slots = 16%nat -> Forall valid_slot slots -> slots !! i = Some (Some a) ->
 scan_identifiers (session_encoding next slots) id (length slots) = Z.of_nat i ->
 removed_words (session_encoding next slots) id = session_encoding next (<[i := None]> slots).
Proof.
 intros Hlen Hvalid Hlookup Hscan. unfold removed_words. rewrite -Hlen Hscan.
 rewrite bool_decide_true; [|lia]. rewrite Nat2Z.id.
 rewrite (encoding_clear_slot next slots i (Some a) Hvalid Hlookup).
 change ([next; Z.of_nat (length (slot_accounts slots))-1] ++ flat_map slot_words (<[i := None]> slots) =
   session_encoding next (<[i := None]> slots)).
 pose proof (slot_accounts_clear_length slots i a Hlookup) as Hcount.
 unfold session_encoding. replace (Z.of_nat (length (slot_accounts slots))-1)
   with (Z.of_nat (length (slot_accounts (<[i := None]> slots)))) by lia.
 reflexivity.
Qed.
Lemma remove_account_absent_identity s id :
 (forall a, In a (accounts s) -> account_id a <> id) -> remove_account s id = s.
Proof.
 intros Hnone. destruct s as [next xs]. unfold remove_account; simpl in *.
 f_equal. apply boolean_filter_identity. intros a Ha. apply Bool.negb_true_iff.
 apply Z.eqb_neq. apply Hnone. exact Ha.
Qed.
Theorem removed_words_represents words s id :
 session_valid s -> represents_session words s ->
 represents_session (removed_words words id) (remove_account s id).
Proof.
 intros Hsession [slots [Hlen [Hvalid [Hperm ->]]]].
 pose proof (scan_identifiers_range (session_encoding (next_id s) slots) id 16) as Hscanrange.
 destruct Hscanrange as [Habs|Hfound].
 - assert (Hnone : remove_account s id = s).
   { apply remove_account_absent_identity. intros a Hin.
     apply (scan_encoded_absent (next_id s) slots id Hvalid).
     - rewrite Hlen. exact Habs.
     - eapply Permutation_in; [symmetry; exact Hperm|exact Hin]. }
   rewrite Hnone. unfold removed_words. rewrite Habs. simpl.
   exists slots. auto.
 - assert (Hfound' : 0 <= scan_identifiers (session_encoding (next_id s) slots) id (length slots)).
   { rewrite Hlen. lia. }
   destruct (scan_encoded_present _ _ _ Hvalid Hfound') as [i [a [Hlookup [Hscan Hid]]]].
   rewrite (removed_encoding_present _ _ _ _ _ Hlen Hvalid Hlookup Hscan).
   rewrite <- Hid. apply remove_slot_represents; assumption.
Qed.
Corollary remove_preserves_representation_and_validity words s id :
 session_valid s -> represents_session words s ->
 session_valid (remove_account s id) /\ represents_session (removed_words words id) (remove_account s id).
Proof. intros Hs Hw. split; [apply remove_preserves_validity|apply removed_words_represents]; assumption. Qed.
