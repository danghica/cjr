(** Metadata updates preserve account identity and the TOTP-relevant state.
    Abstract account order is intentionally separate from physical slot order. *)
From Coq Require Import ZArith List Lia Bool Sorting.Permutation.
From cjr.authenticator Require Import model accounts.
Import ListNotations.
Open Scope Z_scope.
Definition metadata_valid label issuer :=
 (1 <= length label <= 128)%nat /\ (length issuer <= 128)%nat /\
 Forall byte label /\ Forall byte issuer.
Definition metadata_validb label issuer :=
 ((1 <=? length label)%nat && (length label <=? 128)%nat &&
  (length issuer <=? 128)%nat &&
  forallb (fun x => (0 <=? x) && (x <? 256)) label &&
  forallb (fun x => (0 <=? x) && (x <? 256)) issuer)%bool.
Definition with_metadata a label issuer :=
 Account (account_id a) label issuer (account_secret a) (account_digits a) (account_period a).
Definition rename_one id label issuer a :=
 if account_id a =? id then with_metadata a label issuer else a.
Definition rename_account s id label issuer : bool * session :=
 if metadata_validb label issuer then
 match find_account s id with
 | None => (false,s)
 | Some _ => (true,Session (next_id s) (map (rename_one id label issuer) (accounts s)))
 end else (false,s).
Lemma metadata_validb_spec label issuer : metadata_validb label issuer = true <-> metadata_valid label issuer.
Proof.
 unfold metadata_validb,metadata_valid. repeat rewrite andb_true_iff.
 rewrite !Nat.leb_le, !byte_check_spec. tauto.
Qed.
Lemma with_metadata_identity a label issuer :
 account_id (with_metadata a label issuer) = account_id a /\
 account_secret (with_metadata a label issuer) = account_secret a /\
 account_digits (with_metadata a label issuer) = account_digits a /\
 account_period (with_metadata a label issuer) = account_period a.
Proof. repeat split; reflexivity. Qed.
Lemma with_metadata_valid a label issuer :
 account_valid a -> metadata_valid label issuer -> account_valid (with_metadata a label issuer).
Proof.
 unfold account_valid,metadata_valid,with_metadata. simpl.
 intros [Hid [Hl [Hi [Hs [Hlb [Hib [Hsb Hp]]]]]]] [Hlabel [Hissuer [Hlb' Hib']]].
 unfold valid_parameters in Hp. repeat split; tauto.
Qed.
Lemma rename_one_id id label issuer a : account_id (rename_one id label issuer a) = account_id a.
Proof. unfold rename_one. destruct (account_id a =? id); reflexivity. Qed.
Lemma rename_one_crypto id label issuer a :
 account_secret (rename_one id label issuer a) = account_secret a /\
 account_digits (rename_one id label issuer a) = account_digits a /\
 account_period (rename_one id label issuer a) = account_period a.
Proof. unfold rename_one. destruct (account_id a =? id); repeat split; reflexivity. Qed.
Lemma rename_one_valid id label issuer a :
 account_valid a -> metadata_valid label issuer -> account_valid (rename_one id label issuer a).
Proof.
 intros Ha Hmeta. unfold rename_one. destruct (account_id a =? id); [apply with_metadata_valid|]; assumption.
Qed.
Theorem rename_failure_atomic s id label issuer s' :
 rename_account s id label issuer = (false,s') -> s'=s.
Proof.
 unfold rename_account. destruct (metadata_validb label issuer); [destruct (find_account s id)|];
 intros H; inversion H; reflexivity.
Qed.
Theorem rename_preserves_validity s id label issuer success s' :
 session_valid s -> rename_account s id label issuer = (success,s') -> session_valid s'.
Proof.
 intros Hvalid. unfold rename_account.
 destruct (metadata_validb label issuer) eqn:Hmeta; [|intros H; inversion H; subst; exact Hvalid].
 destruct (find_account s id) as [found|]; [|intros H; inversion H; subst; exact Hvalid].
 intros H. inversion H; subst s'.
 apply metadata_validb_spec in Hmeta.
 destruct Hvalid as [Hlen [Hnext [Hdup [Hav Hlt]]]].
 unfold session_valid; simpl. rewrite length_map. split; [assumption|]. split; [assumption|].
 split.
 - rewrite map_map. change (NoDup (map (fun a => account_id (rename_one id label issuer a)) (accounts s))).
   replace (map (fun a => account_id (rename_one id label issuer a)) (accounts s))
    with (map account_id (accounts s)); [exact Hdup|].
   apply map_ext. intros a. symmetry. apply rename_one_id.
 - split.
   + apply Forall_forall. intros a Ha. apply in_map_iff in Ha as [old [<- Hin]].
     apply rename_one_valid; [apply (proj1 (Forall_forall _ _) Hav old Hin)|exact Hmeta].
   + apply Forall_forall. intros a Ha. apply in_map_iff in Ha as [old [<- Hin]].
     rewrite rename_one_id. apply (proj1 (Forall_forall _ _) Hlt old Hin).
Qed.
Lemma find_after_rename xs id label issuer query :
 find (fun a => account_id a =? query) (map (rename_one id label issuer) xs) =
 option_map (rename_one id label issuer) (find (fun a => account_id a =? query) xs).
Proof.
 induction xs as [|a xs IH]; simpl; [reflexivity|].
 rewrite rename_one_id. destruct (account_id a =? query); simpl; [reflexivity|exact IH].
Qed.
Theorem rename_preserves_codes s id label issuer success s' query timestamp :
 rename_account s id label issuer = (success,s') ->
 code_for s' query timestamp = code_for s query timestamp.
Proof.
 unfold rename_account.
 destruct (metadata_validb label issuer); [destruct (find_account s id)|]; intros H;
 inversion H; subst s'; try reflexivity.
 unfold code_for,find_account; simpl. rewrite find_after_rename.
 destruct (find (fun a => account_id a =? query) (accounts s)) as [old|]; simpl; [|reflexivity].
 destruct (rename_one_crypto id label issuer old) as [Hs [Hd Hp]].
 rewrite Hs, Hd, Hp. reflexivity.
Qed.
Definition padded_field (xs : list Z) := xs ++ repeat 0%Z (128-length xs).
Definition slot_words entry :=
 match entry with
 | None => repeat 0%Z 390
 | Some a =>
 [account_id a; account_digits a; account_period a;
  Z.of_nat (length (account_label a)); Z.of_nat (length (account_issuer a));
  Z.of_nat (length (account_secret a))] ++
 padded_field (account_label a) ++ padded_field (account_issuer a) ++ padded_field (account_secret a)
 end.
Fixpoint slot_accounts (slots : list (option account)) :=
 match slots with
 | [] => []
 | None::rest => slot_accounts rest
 | Some a::rest => a::slot_accounts rest
 end.
Definition valid_slot entry := match entry with None => True | Some a => account_valid a end.
Definition session_encoding next slots :=
 [next;Z.of_nat (length (slot_accounts slots))] ++ flat_map slot_words slots.
(** Logical account membership is independent of physical slot order. The
    concrete listing contract still returns the exact physical slot order. *)
Definition represents_session words s := exists slots,
 length slots = 16%nat /\ Forall valid_slot slots /\
 Permutation (slot_accounts slots) (accounts s) /\
 words = session_encoding (next_id s) slots.
Lemma padded_field_length xs : (length xs <= 128)%nat -> length (padded_field xs) = 128%nat.
Proof. intros Hlen. unfold padded_field. rewrite length_app, repeat_length. lia. Qed.
Lemma slot_words_length entry : valid_slot entry -> length (slot_words entry) = 390%nat.
Proof.
 destruct entry as [a|]; simpl; [|intros _; reflexivity].
 unfold valid_slot,account_valid. intros [Hid [Hl [Hi [Hs Hrest]]]].
 rewrite !length_app, !padded_field_length; simpl; try lia.
Qed.
Lemma encoded_slots_length slots : Forall valid_slot slots ->
 length (flat_map slot_words slots) = (390*length slots)%nat.
Proof.
 intros Hvalid. induction Hvalid as [|entry slots Hentry Hslots IH]; simpl; [reflexivity|].
 rewrite length_app, slot_words_length; [rewrite IH; lia|exact Hentry].
Qed.
Theorem represented_session_length words s : represents_session words s -> length words = 6242%nat.
Proof.
 intros [slots [Hlen [Hvalid [Hperm ->]]]]. unfold session_encoding.
 rewrite length_app, encoded_slots_length; [rewrite Hlen; reflexivity|exact Hvalid].
Qed.
Lemma slot_accounts_empty n : slot_accounts (repeat None n) = [].
Proof. induction n; simpl; assumption || reflexivity. Qed.
Lemma encode_empty_slots n : flat_map slot_words (repeat None n) = repeat 0%Z (390*n).
Proof.
 induction n as [|n IH]; [reflexivity|].
 change (repeat 0%Z 390 ++ flat_map slot_words (repeat None n) = repeat 0%Z (390*S n)).
 rewrite IH, <- repeat_app. f_equal. lia.
Qed.
Theorem initialized_session_representation :
 represents_session (1::repeat 0%Z 6241) empty_session.
Proof.
 exists (repeat None 16). split; [apply repeat_length|]. split.
 - apply Forall_forall. intros entry Hentry. apply repeat_spec in Hentry. subst entry. exact I.
 - rewrite slot_accounts_empty. split; [constructor|].
   unfold empty_session,session_encoding; simpl next_id. rewrite slot_accounts_empty, encode_empty_slots.
   reflexivity.
Qed.
Lemma valid_slot_account entry : valid_slot entry ->
 Forall account_valid (match entry with None => [] | Some a => [a] end).
Proof. destruct entry; simpl; intros H; constructor; [exact H|constructor]. Qed.
Lemma slots_accounts_valid slots : Forall valid_slot slots -> Forall account_valid (slot_accounts slots).
Proof.
 intros H. induction H as [|entry slots Hentry Hslots IH]; simpl; [constructor|].
 destruct entry; simpl in *; [constructor; assumption|exact IH].
Qed.
Theorem represented_session_accounts_valid words s :
 represents_session words s -> Forall account_valid (accounts s).
Proof.
 intros [slots [Hlen [Hslots [Hperm Hwords]]]].
 apply (Permutation_Forall Hperm). apply slots_accounts_valid. exact Hslots.
Qed.
Definition entry_id entry := match entry with None => 0 | Some a => account_id a end.
Lemma encoded_slot_identifier slots i entry :
 Forall valid_slot slots -> nth_error slots i = Some entry ->
 nth_error (flat_map slot_words slots) (390*i) = Some (entry_id entry).
Proof.
 revert slots entry. induction i as [|i IH]; intros [|first rest] entry Hvalid Hentry;
 simpl in Hentry; try discriminate.
 - inversion Hentry; subst first. destruct entry; reflexivity.
 - inversion Hvalid as [|? ? Hfirst Hrest]; subst.
   change (nth_error (slot_words first ++ flat_map slot_words rest) (390*S i) = Some (entry_id entry)).
   rewrite nth_error_app2.
   + rewrite slot_words_length; [|exact Hfirst].
     replace (390*S i-390)%nat with (390*i)%nat by lia. apply IH; assumption.
   + rewrite slot_words_length; [lia|exact Hfirst].
Qed.
Lemma session_encoding_identifier next slots i entry :
 Forall valid_slot slots -> nth_error slots i = Some entry ->
 nth_error (session_encoding next slots) (2+390*i) = Some (entry_id entry).
Proof.
 intros Hvalid Hentry. unfold session_encoding. rewrite nth_error_app2; [|simpl; lia].
 simpl length. replace (2+390*i-2)%nat with (390*i)%nat by lia.
 apply encoded_slot_identifier; assumption.
Qed.
Lemma slot_accounts_app xs ys : slot_accounts (xs++ys) = slot_accounts xs ++ slot_accounts ys.
Proof.
 induction xs as [|entry xs IH]; simpl; [reflexivity|].
 destruct entry; simpl; rewrite IH; reflexivity.
Qed.
