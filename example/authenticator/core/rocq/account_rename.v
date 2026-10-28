(** Concrete metadata renaming with overlapping read-only input views. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory memory_application
 input_memory sessions account_validation.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition rename_bound_name name :=
 name="session" \/ name="id" \/ name="label" \/ name="labelLen" \/
 name="issuer" \/ name="issuerLen" \/ name="index" \/ name="entry".
Transparent byte_body copy_body zero_body.
Lemma byte_body_rename_closed name x : rename_bound_name name -> subst name x byte_body = byte_body.
Proof. intros H; unfold rename_bound_name in H; repeat destruct H as [->|H]; try subst name; reflexivity. Qed.
Lemma copy_body_rename_closed name x : rename_bound_name name -> subst name x copy_body = copy_body.
Proof. intros H; unfold rename_bound_name in H; repeat destruct H as [->|H]; try subst name; reflexivity. Qed.
Lemma zero_body_rename_closed name x : rename_bound_name name -> subst name x zero_body = zero_body.
Proof. intros H; unfold rename_bound_name in H; repeat destruct H as [->|H]; try subst name; reflexivity. Qed.
Opaque byte_body copy_body zero_body scan_identifiers.
#[local] Hint Rewrite byte_body_rename_closed copy_body_rename_closed zero_body_rename_closed
 using (unfold rename_bound_name; tauto) : rename_subst.
Ltac rename_args :=
 iStartProof; repeat (simpl; cbn [fill fill_item]; autorewrite with rename_subst;
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 hm_focus e ltac:(fun _ => first [iApply wp_offset; iIntros "!> _" | hm_args_head]) end);
 simpl; cbn [fill fill_item]; autorewrite with rename_subst.
Definition renamed_words words id label issuer :=
 let found := scan_identifiers words id 16 in
 if bool_decide (0 <= found) then
 let offset := (2+390*Z.to_nat found)%nat in
 let wiped := slice_write words (offset+6) (replicate 256 0%Z) in
 let labeled := slice_write wiped (offset+6) label in
 let issued := slice_write labeled (offset+134) issuer in
 <[(offset+4)%nat := Z.of_nat (length issuer)]>
 (<[(offset+3)%nat := Z.of_nat (length label)]> issued)
 else words.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem session_rename_wp heap p words id lp label ip issuer :
 length words = 6242%nat -> (1 <= length label <= 128)%nat -> (length issuer <= 128)%nat ->
 buffer_in heap lp label -> buffer_in heap ip issuer ->
 input_cells heap -∗ array.array_cells p words -∗
 WP call rename_body [pv p;int id;pv lp;int (Z.of_nat (length label));pv ip;int (Z.of_nat (length issuer))]
 {{u, ⌜u = LitV (LitBool
    ((bytes_test label && bytes_test issuer) && bool_decide (0 <= scan_identifiers words id 16)))⌝ ∗
   input_cells heap ∗ array.array_cells p
    (if bytes_test label && bytes_test issuer then renamed_words words id label issuer else words)}}.
Proof.
 intros Hlen Hlabel Hissuer Hlabelview Hissuerview. iIntros "Hheap Hs".
 unfold call at 1. unfold rename_body,args. hm_args. iApply wp_app. hm_pure.
 repeat (rewrite bool_decide_true; [|lia]).
 iApply wp_if_true. rename_args.
 iApply (wp_wand with "[Hheap]").
 { iApply (bytes_view_reduced_wp heap lp label Hlabelview with "Hheap"). }
 iIntros (u) "[%Hu Hheap]". subst u. rename_args.
 iApply (wp_wand with "[Hheap]").
 { iApply (bytes_view_reduced_wp heap ip issuer Hissuerview with "Hheap"). }
 iIntros (u) "[%Hu Hheap]". subst u. rename_args.
 destruct (bytes_test label && bytes_test issuer)%bool eqn:Hbytes.
 - iApply wp_if_true. hm_admin.
   match goal with |- envs_entails _ (WP Let ?x ?e ?b {{_}}) =>
     iApply (wp_bind [LetCtx x b]) end.
   iApply (wp_wand with "[Hs]").
   { iApply (session_find_wp p words id Hlen with "Hs"). }
   iIntros (u) "[%Hu Hs]". subst u. hm_pure.
   destruct (bool_decide (0 <= scan_identifiers words id 16)) eqn:Hfound.
   + apply bool_decide_eq_true in Hfound. iApply wp_if_true.
     pose proof (scan_identifiers_range words id 16) as Hrange.
     set (index := Z.to_nat (scan_identifiers words id 16)).
     assert (Hindex : (index < 16)%nat) by (unfold index; lia).
     assert (Hki : Z.of_nat index = scan_identifiers words id 16) by (unfold index; lia).
     set (offset := (2+390*index)%nat).
     assert (Hbound : (offset+390 <= length words)%nat).
     { unfold offset. rewrite Hlen. change (2+390*index+390 <= 2+390*16)%nat. lia. }
     rename_args.
     assert (Haddr : p + (2 + scan_identifiers words id 16 * 390) = p + Z.of_nat offset).
     { unfold offset. rewrite Nat2Z.inj_add Nat2Z.inj_mul Hki. ring. }
     rewrite Haddr.
     replace (p+Z.of_nat offset+6) with (p+Z.of_nat (offset+6)) by (rewrite Nat2Z.inj_add; simpl; ring).
     iDestruct (cells_slice_acc p words (offset+6) 256 ltac:(lia) with "Hs") as "[Hslice Hclose]".
     iApply (wp_wand with "[Hslice]").
     { iApply (zero_reduced_wp _ _ 256 with "Hslice"). rewrite length_take length_drop. lia. }
     iIntros (u) "[%Hu Hslice]". subst u.
     assert (Hdrop : drop 256 (take 256 (drop (offset+6) words)) = []).
     { apply drop_ge. rewrite length_take. lia. }
     iEval (rewrite Hdrop app_nil_r) in "Hslice".
     iDestruct ("Hclose" $! (replicate 256 0%Z) with "[] Hslice") as "Hs".
     { iPureIntro. apply length_replicate. }
     set (wiped := slice_write words (offset+6) (replicate 256 0%Z)).
     iAssert (array.array_cells p wiped) with "[Hs]" as "Hs".
     { unfold wiped,slice_write. rewrite length_replicate. iExact "Hs". }
     assert (Hwiped : length wiped = length words).
     { unfold wiped. apply slice_write_length. rewrite length_replicate. lia. }
     iApply wp_seq. rename_args.
     replace (p+Z.of_nat offset+6) with (p+Z.of_nat (offset+6)) by (rewrite Nat2Z.inj_add; simpl; ring).
     iApply (wp_wand with "[Hheap Hs]").
     { iApply (copy_view_slice_reduced_wp heap lp label p wiped (offset+6) (length label)
         Hlabelview ltac:(lia) ltac:(lia) with "Hheap Hs"). }
     iIntros (u) "[%Hu [Hheap Hs]]". subst u.
     assert (Htake_label : take (length label) label = label) by (apply take_ge; lia).
     iEval (rewrite Htake_label) in "Hs".
     set (labeled := slice_write wiped (offset+6) label).
     assert (Hlabeled : length labeled = length words).
     { unfold labeled. rewrite <- Hwiped. apply slice_write_length. lia. }
     iApply wp_seq. rename_args.
     replace (p+Z.of_nat offset+134) with (p+Z.of_nat (offset+134)) by (rewrite Nat2Z.inj_add; simpl; ring).
     iApply (wp_wand with "[Hheap Hs]").
     { iApply (copy_view_slice_reduced_wp heap ip issuer p labeled (offset+134) (length issuer)
         Hissuerview ltac:(lia) ltac:(lia) with "Hheap Hs"). }
     iIntros (u) "[%Hu [Hheap Hs]]". subst u.
     assert (Htake_issuer : take (length issuer) issuer = issuer) by (apply take_ge; lia).
     iEval (rewrite Htake_issuer) in "Hs".
     set (issued := slice_write labeled (offset+134) issuer).
     assert (Hissued : length issued = length words).
     { unfold issued. rewrite <- Hlabeled. apply slice_write_length. lia. }
     iApply wp_seq. hm_pure.
     replace (p+Z.of_nat offset+3) with (p+Z.of_nat (offset+3)) by (rewrite Nat2Z.inj_add; simpl; ring).
     assert (Hlabelpos : (offset+3 < length issued)%nat) by lia.
     destruct (lookup_lt_is_Some_2 issued _ Hlabelpos) as [old Hlookup].
     iDestruct (big_sepL_insert_acc with "Hs") as "[Hcell Hclose]"; [exact Hlookup|].
     iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" $! (Z.of_nat (length label)) with "Hcell") as "Hs". hm_pure.
     replace (p+Z.of_nat offset+4) with (p+Z.of_nat (offset+4)) by (rewrite Nat2Z.inj_add; simpl; ring).
     assert (Hissuerpos : (offset+4 < length (<[(offset+3)%nat:=Z.of_nat (length label)]> issued))%nat).
     { rewrite length_insert. lia. }
     destruct (lookup_lt_is_Some_2 _ _ Hissuerpos) as [old' Hlookup'].
     iDestruct (big_sepL_insert_acc with "Hs") as "[Hcell Hclose]"; [exact Hlookup'|].
     iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" $! (Z.of_nat (length issuer)) with "Hcell") as "Hs". hm_pure.
     rewrite /renamed_words bool_decide_true; last exact Hfound.
     fold index offset wiped labeled issued. iFrame. done.
   + apply bool_decide_eq_false in Hfound. iApply wp_if_false. iApply wp_value'.
     rewrite /renamed_words bool_decide_false; last exact Hfound. iFrame. done.
 - iApply wp_if_false. iApply wp_value'. iFrame. done.
Qed.
Theorem session_rename_all_lengths_wp heap p words id lp label ip issuer :
 length words = 6242%nat -> buffer_in heap lp label -> buffer_in heap ip issuer ->
 input_cells heap -∗ array.array_cells p words -∗
 WP call rename_body [pv p;int id;pv lp;int (Z.of_nat (length label));pv ip;int (Z.of_nat (length issuer))]
 {{u, ⌜u = LitV (LitBool
   (if bool_decide ((1 <= length label <= 128)%nat /\ (length issuer <= 128)%nat)
    then (bytes_test label && bytes_test issuer) && bool_decide (0 <= scan_identifiers words id 16)
    else false))⌝ ∗ input_cells heap ∗ array.array_cells p
   (if bool_decide ((1 <= length label <= 128)%nat /\ (length issuer <= 128)%nat)
    then (if bytes_test label && bytes_test issuer then renamed_words words id label issuer else words)
    else words)}}.
Proof.
 intros Hlen Hlabelview Hissuerview. iIntros "Hheap Hs".
 destruct (decide ((1 <= length label <= 128)%nat /\ (length issuer <= 128)%nat)) as [Hbounds|Hbounds].
 - rewrite bool_decide_true; last exact Hbounds.
   destruct Hbounds as [Hlabel Hissuer].
   iApply (session_rename_wp heap p words id lp label ip issuer Hlen Hlabel Hissuer
     Hlabelview Hissuerview with "Hheap Hs").
 - rewrite bool_decide_false; last exact Hbounds.
   iApply (rename_length_rejected_wp p id lp (Z.of_nat (length label)) ip
     (Z.of_nat (length issuer)) (input_cells heap ∗ array.array_cells p words)%I with "[Hheap Hs]").
   + intros Hvalid. apply Hbounds. lia.
   + iFrame.
Qed.
End proofs.
